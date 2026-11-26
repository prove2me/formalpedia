-- Prove2me | Theorems.Thm_P2M_FriedCrossing_Spectral_E__mirror_bf3c94cb1a0c
-- name    : P2M_FriedCrossing_Spectral_E__mirror_bf3c94cb1a0c
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:50:44.690798+00:00
-- url     : https://prove2.me/theorems/36a81c9c-df60-591c-adbf-fc917c604ce4
-- title:
--   P2 M Fried Crossing Spectral E  mirror bf3c94cb1a0c: P2 M Fried Crossing Spectral E  mirror bf3c94cb1a0c
-- statement:
--   The P2 M Fried Crossing Spectral E  mirror bf3c94cb1a0c construction uses the P2 M Fried Crossing Spectral E  mirror bf3c94cb1a0c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L593-L597
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L593-L597

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Spectral
open ClusterMatrix

theorem P2M_FriedCrossing_Spectral_E__mirror_bf3c94cb1a0c {A : Matrix (Fin 4) (Fin 4) ℝ} {M : Matrix (Fin 2) (Fin 2) ℝ} {s : ℝ}
    (hM : M = s • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (hA : ∀ z, A.charpoly.eval z = (z - s) ^ 3 * (z + s)) : E₂ A M = -s ^ 2 := by sorry

alias «FriedCrossing».«Spectral».«E₂_mirror» := P2M_FriedCrossing_Spectral_E__mirror_bf3c94cb1a0c
