-- Prove2me | Theorems.Thm_P2M_FriedCrossing_Spectral_E__pinned_8575cb4e933f
-- name    : P2M_FriedCrossing_Spectral_E__pinned_8575cb4e933f
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:50:50.092031+00:00
-- url     : https://prove2.me/theorems/3dcef30d-60a0-547b-8045-bb660980d713
-- title:
--   P2 M Fried Crossing Spectral E  pinned 8575cb4e933f: P2 M Fried Crossing Spectral E  pinned 8575cb4e933f
-- statement:
--   The P2 M Fried Crossing Spectral E  pinned 8575cb4e933f construction uses the P2 M Fried Crossing Spectral E  pinned 8575cb4e933f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L606-L609
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L606-L609

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Spectral
open ClusterMatrix

theorem P2M_FriedCrossing_Spectral_E__pinned_8575cb4e933f {A : Matrix (Fin 4) (Fin 4) ℝ} {M : Matrix (Fin 2) (Fin 2) ℝ}
    (hdet : M.det = 0) (hA : ∀ z, A.charpoly.eval z = z ^ 3 * (z - M.trace)) : E₂ A M = 0 := by sorry

alias «FriedCrossing».«Spectral».«E₂_pinned» := P2M_FriedCrossing_Spectral_E__pinned_8575cb4e933f
