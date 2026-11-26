-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_rep_mk
-- name    : SemigroupBetti.GenData.rep_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:00:53.690116+00:00
-- url     : https://prove2.me/theorems/b1afdf61-236a-467e-9bfe-eb7b0ee46a35
-- title:
--   Gen Data: rep mk
-- statement:
--   The Gen Data construction uses the rep mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Bridge.lean#L104-L106
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Bridge.lean#L104-L106

module
public import Definitions.Def_SemigroupBetti_Fiber
public import Definitions.Def_SemigroupBetti_Bridge
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset MvPolynomial
open SemigroupBetti.GenData
variable (G : GenData) (K : Type*) [Field K]

theorem SemigroupBetti.GenData.rep_mk {d : ℕ} (C : (G.nabla d).ConnectedComponent) :
    (G.nabla d).connectedComponentMk (⟨G.rep C, (Quot.out C).2⟩ : G.fiber d) = C := by sorry
