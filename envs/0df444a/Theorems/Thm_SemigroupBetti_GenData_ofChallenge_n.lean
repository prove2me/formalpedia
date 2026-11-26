-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_ofChallenge_n
-- name    : SemigroupBetti.GenData.ofChallenge_n
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:52:48.140859+00:00
-- url     : https://prove2.me/theorems/5b53b08f-a0df-5b1c-a477-e708a0bd9f31
-- title:
--   Gen Data: of Challenge n
-- statement:
--   The Gen Data construction uses the of Challenge n property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Bridge.lean#L364-L368
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Bridge.lean#L364-L368

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

theorem SemigroupBetti.GenData.ofChallenge_n : (ofChallenge n hpos hmono hgcd hmin).n = n := by sorry
