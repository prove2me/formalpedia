-- Prove2me | Theorems.Thm_P2M_FriedCrossing_Derived_contDiff_E_f_b048a987d2d2
-- name    : P2M_FriedCrossing_Derived_contDiff_E_f_b048a987d2d2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:50:44.331272+00:00
-- url     : https://prove2.me/theorems/d34de34b-1a8a-4cf8-b7b9-a1e3671b8f0f
-- title:
--   P2 M Fried Crossing Derived cont Diff E f b048a987d2d2: P2 M Fried Crossing Derived cont Diff E f b048a987d2d2
-- statement:
--   The P2 M Fried Crossing Derived cont Diff E f b048a987d2d2 construction uses the P2 M Fried Crossing Derived cont Diff E f b048a987d2d2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L519-L520
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L519-L520

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Derived
open Regularity HQuot Hadamard ClusterMatrix Ledger
variable {M : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ} {A : ℝ → ℝ → Matrix (Fin 4) (Fin 4) ℝ}
  {sStar : ℝ → ℝ}

theorem P2M_FriedCrossing_Derived_contDiff_E_f_b048a987d2d2 (h : ClusterC3 M A) : ContDiff ℝ 3 fun q : ℝ × ℝ => E₁f M A q.1 q.2 := by sorry

alias «FriedCrossing».«Derived».«contDiff_E₁f» := P2M_FriedCrossing_Derived_contDiff_E_f_b048a987d2d2
