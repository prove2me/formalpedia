-- Prove2me | Theorems.Thm_P2M_FriedCrossing_Spectral_E__pinned_89a5c3e78b6a
-- name    : P2M_FriedCrossing_Spectral_E__pinned_89a5c3e78b6a
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:50:49.81931+00:00
-- url     : https://prove2.me/theorems/f69bfe53-4fc7-4f5f-b599-c5629e007ac1
-- title:
--   P2 M Fried Crossing Spectral E  pinned 89a5c3e78b6a: P2 M Fried Crossing Spectral E  pinned 89a5c3e78b6a
-- statement:
--   PINNING (input D) on the matrices: det M(0,τ) = 0 and spec A(0,τ) = {0,0,0,tr M(0,τ)} ⇒
--   e₁(0,τ) = 0, e₂(0,τ) = 0.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L601-L604
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L601-L604

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Spectral
open ClusterMatrix

theorem P2M_FriedCrossing_Spectral_E__pinned_89a5c3e78b6a {A : Matrix (Fin 4) (Fin 4) ℝ} {M : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : ∀ z, A.charpoly.eval z = z ^ 3 * (z - M.trace)) : E₁ A M = 0 := by sorry

alias «FriedCrossing».«Spectral».«E₁_pinned» := P2M_FriedCrossing_Spectral_E__pinned_89a5c3e78b6a
