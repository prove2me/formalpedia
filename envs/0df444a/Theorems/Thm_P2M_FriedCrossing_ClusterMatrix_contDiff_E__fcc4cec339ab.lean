-- Prove2me | Theorems.Thm_P2M_FriedCrossing_ClusterMatrix_contDiff_E__fcc4cec339ab
-- name    : P2M_FriedCrossing_ClusterMatrix_contDiff_E__fcc4cec339ab
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:42:54.506058+00:00
-- url     : https://prove2.me/theorems/aa536051-70b4-4f02-8f0c-8ccb30d57514
-- title:
--   P2 M Fried Crossing Cluster Matrix cont Diff E  fcc4cec339ab: P2 M Fried Crossing Cluster Matrix cont Diff E  fcc4cec339ab
-- statement:
--   The P2 M Fried Crossing Cluster Matrix cont Diff E  fcc4cec339ab construction uses the P2 M Fried Crossing Cluster Matrix cont Diff E  fcc4cec339ab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L118-L121
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L118-L121

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.ClusterMatrix
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : WithTop ℕ∞}

theorem P2M_FriedCrossing_ClusterMatrix_contDiff_E__fcc4cec339ab {A : E → Matrix (Fin 4) (Fin 4) ℝ} {M : E → Matrix (Fin 2) (Fin 2) ℝ}
    (hA : ∀ i j, ContDiff ℝ k fun x => A x i j) (hM : ∀ i j, ContDiff ℝ k fun x => M x i j) :
    ContDiff ℝ k fun x => E₁ (A x) (M x) := by sorry

alias «FriedCrossing».«ClusterMatrix».«contDiff_E₁» := P2M_FriedCrossing_ClusterMatrix_contDiff_E__fcc4cec339ab
