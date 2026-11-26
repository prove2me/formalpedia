-- Prove2me | Theorems.Thm_P2M_FriedCrossing_ClusterMatrix_contDiff_c__fa11d2ba6eea
-- name    : P2M_FriedCrossing_ClusterMatrix_contDiff_c__fa11d2ba6eea
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:48:44.968405+00:00
-- url     : https://prove2.me/theorems/20fa2fb4-2078-56d6-a128-72ac504cf716
-- title:
--   P2 M Fried Crossing Cluster Matrix cont Diff c  fa11d2ba6eea: P2 M Fried Crossing Cluster Matrix cont Diff c  fa11d2ba6eea
-- statement:
--   The P2 M Fried Crossing Cluster Matrix cont Diff c  fa11d2ba6eea construction uses the P2 M Fried Crossing Cluster Matrix cont Diff c  fa11d2ba6eea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L106-L108
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L106-L108

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.ClusterMatrix
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : WithTop ℕ∞}

theorem P2M_FriedCrossing_ClusterMatrix_contDiff_c__fa11d2ba6eea {A : E → Matrix (Fin 4) (Fin 4) ℝ}
    (h : ∀ i j, ContDiff ℝ k fun x => A x i j) : ContDiff ℝ k fun x => c₂ (A x) := by sorry

alias «FriedCrossing».«ClusterMatrix».«contDiff_c₂» := P2M_FriedCrossing_ClusterMatrix_contDiff_c__fa11d2ba6eea
