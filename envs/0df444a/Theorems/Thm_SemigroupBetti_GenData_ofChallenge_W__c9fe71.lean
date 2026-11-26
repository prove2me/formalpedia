-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_ofChallenge_W__c9fe71
-- name    : SemigroupBetti.GenData.ofChallenge_W
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T03:09:29.592796+00:00
-- url     : https://prove2.me/theorems/c9fe713b-fef2-4f37-b2eb-67ceb0ea018d
-- title:
--   Gen Data: of Challenge W
-- statement:
--   `W = w / gcd(a, b, w)` is the `normalizedWidth` of `Challenge.lean` (unfolded).
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Bridge.lean#L373-L374
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Bridge.lean#L373-L374

module
public import Definitions.Def_SemigroupBetti_Fiber
public import Definitions.Def_SemigroupBetti_Bridge
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset MvPolynomial
open SemigroupBetti.GenData
variable (n : Fin 4 → ℕ) (hpos : 0 < n 0) (hmono : StrictMono n)
  (hgcd : Finset.univ.gcd n = 1)
  (hmin : ∀ i : Fin 4, n i ∉ AddSubmonoid.closure (n '' {j | j ≠ i}))

theorem SemigroupBetti.GenData.ofChallenge_W : (ofChallenge n hpos hmono hgcd hmin).W =
    (n 3 - n 0) / Nat.gcd (n 1 - n 0) (Nat.gcd (n 2 - n 0) (n 3 - n 0)) := by sorry
