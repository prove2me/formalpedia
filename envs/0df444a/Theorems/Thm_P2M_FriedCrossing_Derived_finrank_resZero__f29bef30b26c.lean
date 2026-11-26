-- Prove2me | Theorems.Thm_P2M_FriedCrossing_Derived_finrank_resZero__f29bef30b26c
-- name    : P2M_FriedCrossing_Derived_finrank_resZero__f29bef30b26c
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:49:41.806508+00:00
-- url     : https://prove2.me/theorems/2523cde8-150c-5fe8-b533-88ecf4bf9fd8
-- title:
--   P2 M Fried Crossing Derived finrank res Zero  f29bef30b26c: P2 M Fried Crossing Derived finrank res Zero  f29bef30b26c
-- statement:
--   The P2 M Fried Crossing Derived finrank res Zero  f29bef30b26c construction uses the P2 M Fried Crossing Derived finrank res Zero  f29bef30b26c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L411-L413
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L411-L413

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Derived
open Regularity HQuot Hadamard ClusterMatrix Ledger

theorem P2M_FriedCrossing_Derived_finrank_resZero__f29bef30b26c (M : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (θ τ : ℝ) :
    Module.finrank ℝ (resZero₁ M θ τ) = (M θ τ).charpoly.rootMultiplicity 0 := by sorry

alias «FriedCrossing».«Derived».«finrank_resZero₁» := P2M_FriedCrossing_Derived_finrank_resZero__f29bef30b26c
