-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_ofChallenge_w
-- name    : SemigroupBetti.GenData.ofChallenge_w
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:09:26.653937+00:00
-- url     : https://prove2.me/theorems/06d6104e-e03f-4c53-8eca-fc2bac508159
-- title:
--   Gen Data: of Challenge w
-- statement:
--   The Gen Data construction uses the of Challenge w property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Bridge.lean#L370-L370
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Bridge.lean#L370-L370

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

theorem SemigroupBetti.GenData.ofChallenge_w : (ofChallenge n hpos hmono hgcd hmin).w = n 3 - n 0 := by sorry
