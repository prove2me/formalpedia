-- Prove2me | Theorems.Thm_P2M_FriedCrossing_ClusterMatrix_contDiff_E__fe65e108e397
-- name    : P2M_FriedCrossing_ClusterMatrix_contDiff_E__fe65e108e397
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T04:48:55.203984+00:00
-- url     : https://prove2.me/theorems/1ca52844-49af-4d8d-902c-bb70abee3ce5
-- title:
--   P2 M Fried Crossing Cluster Matrix cont Diff E  fe65e108e397: P2 M Fried Crossing Cluster Matrix cont Diff E  fe65e108e397
-- statement:
--   The P2 M Fried Crossing Cluster Matrix cont Diff E  fe65e108e397 construction uses the P2 M Fried Crossing Cluster Matrix cont Diff E  fe65e108e397 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L123-L127
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L123-L127

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.ClusterMatrix
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : WithTop ℕ∞}

theorem P2M_FriedCrossing_ClusterMatrix_contDiff_E__fe65e108e397 {A : E → Matrix (Fin 4) (Fin 4) ℝ} {M : E → Matrix (Fin 2) (Fin 2) ℝ}
    (hA : ∀ i j, ContDiff ℝ k fun x => A x i j) (hM : ∀ i j, ContDiff ℝ k fun x => M x i j) :
    ContDiff ℝ k fun x => E₂ (A x) (M x) := by sorry

alias «FriedCrossing».«ClusterMatrix».«contDiff_E₂» := P2M_FriedCrossing_ClusterMatrix_contDiff_E__fe65e108e397
