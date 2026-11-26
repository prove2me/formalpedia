-- Prove2me | Theorems.Thm_P2M_FriedCrossing_Spectral_E__mirror_535f6e567606
-- name    : P2M_FriedCrossing_Spectral_E__mirror_535f6e567606
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:50:37.557071+00:00
-- url     : https://prove2.me/theorems/0a07d7a6-2ee3-48c5-a04e-c78c9f86a9c9
-- title:
--   P2 M Fried Crossing Spectral E  mirror 535f6e567606: P2 M Fried Crossing Spectral E  mirror 535f6e567606
-- statement:
--   MIRROR (input A) on the matrices: M(θ,0) = s*·1 and spec A(θ,0) = {s*,s*,s*,−s*} ⇒
--   e₁(θ,0) = 0, e₂(θ,0) = −s*².
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L587-L591
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L587-L591

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Spectral
open ClusterMatrix

theorem P2M_FriedCrossing_Spectral_E__mirror_535f6e567606 {A : Matrix (Fin 4) (Fin 4) ℝ} {M : Matrix (Fin 2) (Fin 2) ℝ} {s : ℝ}
    (hM : M = s • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (hA : ∀ z, A.charpoly.eval z = (z - s) ^ 3 * (z + s)) : E₁ A M = 0 := by sorry

alias «FriedCrossing».«Spectral».«E₁_mirror» := P2M_FriedCrossing_Spectral_E__mirror_535f6e567606
