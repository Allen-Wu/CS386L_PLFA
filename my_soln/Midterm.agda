-- Name: Shiyu Wu
-- EID: sw37625
module plfa.part1.Midterm where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
-- you can add any import definitions that you need
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; _>_; z≤n; s≤s; _≤?_; _<_)
open import Data.Nat.Properties using (+-assoc; +-suc; *-suc; +-comm; +-identityʳ; *-comm; *-distribʳ-+)
open import Relation.Nullary using (yes; no)

-- used for rewrite
simplify : ∀ {A : Set} (x : A) → x ≡ x
simplify x = refl

sum : ℕ → ℕ
sum 0 = 0
sum (suc n) = sum n + n

-- Problem 1
-- remove the "postulate" and prove this theorem, which is a version of
--   sum n ≡ n * (n - 1) / 2
-- Use induction to prove
simple : ∀ (n : ℕ) → sum (suc n) * 2 ≡ (suc n) * n
-- Base trivial case
simple zero =
  begin
    sum (suc zero) * 2
  ≡⟨⟩
    (sum zero + zero) * 2
  ≡⟨⟩
    zero
  ≡⟨⟩
    (suc zero) * zero
  ∎
-- Inductive case
-- Target : sum (suc (suc n)) * 2 == (suc (suc n)) * (suc n)
simple (suc n) =
  begin
    sum (suc (suc n)) * 2
  ≡⟨⟩
    ((sum (suc n)) + (suc n)) * 2
  ≡⟨ (*-distribʳ-+) (2) (sum (suc n)) (suc n) ⟩
    (sum (suc n)) * 2 + (suc n) * 2
  ≡⟨ cong (_+ (suc n) * 2) (simple n) ⟩
    (suc n) * n + (suc n) * 2
  ≡⟨ cong (_+ (suc n) * 2) (*-comm (suc n) n) ⟩
    n * (suc n) + (suc n) * 2
  ≡⟨ cong ((n * (suc n)) +_) (*-comm (suc n) 2) ⟩
    n * (suc n) + 2 * (suc n)
  ≡⟨ sym (*-distribʳ-+ (suc n) n 2)  ⟩
    (n + 2) * (suc n)
  ≡⟨ cong (_* (suc n)) (+-suc n 1) ⟩
    (suc (n + 1)) * (suc n)
  ≡⟨ cong (λ x → (suc x) * (suc n)) (+-suc n 0) ⟩
    (suc (suc (n + 0))) * (suc n)
  ≡⟨ cong (λ x → ((suc (suc x)) * (suc n))) (+-identityʳ n) ⟩
    (suc (suc n)) * (suc n)
  ∎

-- Problem 2
-- remove the postulate and implement this function, which gives an Natural
-- number approximation of square root
-- Remark: This is an iterative approach with time complexity O(sqrt(n))
helper : ℕ → ℕ → ℕ → ℕ
helper m zero p = p
helper m (suc n) p with ((suc p) * (suc p) ≤? m)
...              | yes _ = (helper m n (suc p))
...              | no  _ = p

sqrt : ℕ → ℕ
sqrt zero = zero
sqrt (suc n) = helper (suc n) (suc n) zero


-- you can run these test cases
_ : sqrt 0 ≡ 0
_ = refl
_ : sqrt 1 ≡ 1
_ = refl
_ : sqrt 2 ≡ 1
_ = refl
_ : sqrt 3 ≡ 1
_ = refl
_ : sqrt 4 ≡ 2
_ = refl
_ : sqrt 5 ≡ 2
_ = refl
_ : sqrt 6 ≡ 2
_ = refl
_ : sqrt 7 ≡ 2
_ = refl
_ : sqrt 8 ≡ 2
_ = refl
_ : sqrt 9 ≡ 3
_ = refl
_ : sqrt 10 ≡ 3
_ = refl
_ : sqrt 11 ≡ 3
_ = refl
_ : sqrt 12 ≡ 3
_ = refl
_ : sqrt 13 ≡ 3
_ = refl
_ : sqrt 14 ≡ 3
_ = refl
_ : sqrt 15 ≡ 3
_ = refl
_ : sqrt 16 ≡ 4
_ = refl
_ : sqrt 17 ≡ 4
_ = refl
_ : sqrt 18 ≡ 4
_ = refl
_ : sqrt 19 ≡ 4
_ = refl
_ : sqrt 20 ≡ 4
_ = refl
_ : sqrt 21 ≡ 4
_ = refl
_ : sqrt 22 ≡ 4
_ = refl
_ : sqrt 23 ≡ 4
_ = refl
_ : sqrt 24 ≡ 4
_ = refl
_ : sqrt 24 ≡ 4
_ = refl
_ : sqrt 24 ≡ 4
_ = refl
_ : sqrt 25 ≡ 5
_ = refl
_ : sqrt 26 ≡ 5
_ = refl
_ : sqrt 27 ≡ 5
_ = refl
_ : sqrt 35 ≡ 5
_ = refl
_ : sqrt 36 ≡ 6
_ = refl
_ : sqrt 37 ≡ 6
_ = refl
_ : sqrt 48 ≡ 6
_ = refl
_ : sqrt 49 ≡ 7
_ = refl
_ : sqrt 80 ≡ 8
_ = refl
_ : sqrt 81 ≡ 9
_ = refl
_ : sqrt 99 ≡ 9
_ = refl
_ : sqrt 100 ≡ 10
_ = refl
_ : sqrt 101 ≡ 10
_ = refl
