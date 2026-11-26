-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_pairsOf_pos
-- name    : SemigroupBetti.GenData.pairsOf_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:05:47.268196+00:00
-- url     : https://prove2.me/theorems/a80c564f-dd63-4e10-96c7-795a54c961d3
-- title:
--   Gen Data: pairs Of pos
-- statement:
--   The Gen Data construction uses the pairs Of pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Exceptional.lean#L71-L78
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Exceptional.lean#L71-L78

module
public import Definitions.Def_SemigroupBetti_Arith
public import Definitions.Def_SemigroupBetti_Exceptional
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)

theorem SemigroupBetti.GenData.pairsOf_pos {F : Finset ℕ} {K : Finset (Fin 4)} {i k : Fin 4} (hik : i ≠ k)
    (hKe : K = {i, k}) (hF : ∀ d ∈ F, G.IsSplit d K) :
    ∀ x ∈ G.pairsOf F K i k, 1 ≤ x.1 ∧ 1 ≤ x.2 := by sorry
