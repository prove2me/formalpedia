-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_pairsOf_antichain
-- name    : SemigroupBetti.GenData.pairsOf_antichain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:04:41.320301+00:00
-- url     : https://prove2.me/theorems/54e86dff-9eca-50a6-b858-08609de58881
-- title:
--   Gen Data: pairs Of antichain
-- statement:
--   The Gen Data construction uses the pairs Of antichain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Exceptional.lean#L60-L69
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Exceptional.lean#L60-L69

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

theorem SemigroupBetti.GenData.pairsOf_antichain {F : Finset ℕ} {K : Finset (Fin 4)} {i k : Fin 4} (hik : i ≠ k)
    (hKe : K = {i, k}) (hF : ∀ d ∈ F, G.IsSplit d K) : IsPairAntichain (G.pairsOf F K i k) := by sorry
