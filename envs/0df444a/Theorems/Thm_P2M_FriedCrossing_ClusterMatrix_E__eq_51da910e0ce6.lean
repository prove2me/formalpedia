-- Prove2me | Theorems.Thm_P2M_FriedCrossing_ClusterMatrix_E__eq_51da910e0ce6
-- name    : P2M_FriedCrossing_ClusterMatrix_E__eq_51da910e0ce6
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T04:48:25.205023+00:00
-- url     : https://prove2.me/theorems/8059fe8e-a572-44e5-9a53-f335b1166c43
-- title:
--   P2 M Fried Crossing Cluster Matrix E  eq 51da910e0ce6: P2 M Fried Crossing Cluster Matrix E  eq 51da910e0ce6
-- statement:
--   With the locked branches the eigenvalues of M, these are the pure-zeros file's `e₁of`,
--   `e₂of`.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L63-L65
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L63-L65

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.ClusterMatrix

theorem P2M_FriedCrossing_ClusterMatrix_E__eq_51da910e0ce6 (A : Matrix (Fin 4) (Fin 4) ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ) {scl snc : ℝ}
    (hs : scl + snc = M.trace) : E₁ A M = PureZeros.e₁of (c₁ A) scl snc := by sorry

alias «FriedCrossing».«ClusterMatrix».«E₁_eq» := P2M_FriedCrossing_ClusterMatrix_E__eq_51da910e0ce6
