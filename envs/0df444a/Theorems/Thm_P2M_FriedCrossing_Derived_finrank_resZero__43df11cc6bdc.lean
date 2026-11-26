-- Prove2me | Theorems.Thm_P2M_FriedCrossing_Derived_finrank_resZero__43df11cc6bdc
-- name    : P2M_FriedCrossing_Derived_finrank_resZero__43df11cc6bdc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:50:27.031272+00:00
-- url     : https://prove2.me/theorems/42782b00-46c2-4d1a-8144-8f0e2603b54e
-- title:
--   P2 M Fried Crossing Derived finrank res Zero  43df11cc6bdc: P2 M Fried Crossing Derived finrank res Zero  43df11cc6bdc
-- statement:
--   The P2 M Fried Crossing Derived finrank res Zero  43df11cc6bdc construction uses the P2 M Fried Crossing Derived finrank res Zero  43df11cc6bdc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L415-L417
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L415-L417

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Derived
open Regularity HQuot Hadamard ClusterMatrix Ledger

theorem P2M_FriedCrossing_Derived_finrank_resZero__43df11cc6bdc (A : ℝ → ℝ → Matrix (Fin 4) (Fin 4) ℝ) (θ τ : ℝ) :
    Module.finrank ℝ (resZero₂ A θ τ) = (A θ τ).charpoly.rootMultiplicity 0 := by sorry

alias «FriedCrossing».«Derived».«finrank_resZero₂» := P2M_FriedCrossing_Derived_finrank_resZero__43df11cc6bdc
