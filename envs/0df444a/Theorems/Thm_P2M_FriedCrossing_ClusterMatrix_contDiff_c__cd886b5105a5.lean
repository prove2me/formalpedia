-- Prove2me | Theorems.Thm_P2M_FriedCrossing_ClusterMatrix_contDiff_c__cd886b5105a5
-- name    : P2M_FriedCrossing_ClusterMatrix_contDiff_c__cd886b5105a5
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T04:49:20.748293+00:00
-- url     : https://prove2.me/theorems/2d48ca6d-5122-456b-b209-e5906f89cddc
-- title:
--   P2 M Fried Crossing Cluster Matrix cont Diff c  cd886b5105a5: P2 M Fried Crossing Cluster Matrix cont Diff c  cd886b5105a5
-- statement:
--   The P2 M Fried Crossing Cluster Matrix cont Diff c  cd886b5105a5 construction uses the P2 M Fried Crossing Cluster Matrix cont Diff c  cd886b5105a5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L102-L104
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L102-L104

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.ClusterMatrix
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : WithTop ℕ∞}

theorem P2M_FriedCrossing_ClusterMatrix_contDiff_c__cd886b5105a5 {A : E → Matrix (Fin 4) (Fin 4) ℝ}
    (h : ∀ i j, ContDiff ℝ k fun x => A x i j) : ContDiff ℝ k fun x => c₁ (A x) := by sorry

alias «FriedCrossing».«ClusterMatrix».«contDiff_c₁» := P2M_FriedCrossing_ClusterMatrix_contDiff_c__cd886b5105a5
