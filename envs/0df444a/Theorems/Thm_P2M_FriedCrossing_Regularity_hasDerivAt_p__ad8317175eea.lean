-- Prove2me | Theorems.Thm_P2M_FriedCrossing_Regularity_hasDerivAt_p__ad8317175eea
-- name    : P2M_FriedCrossing_Regularity_hasDerivAt_p__ad8317175eea
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:40:24.263146+00:00
-- url     : https://prove2.me/theorems/56c6734a-9f78-57c7-98a2-d390fac95780
-- title:
--   P2 M Fried Crossing Regularity has Deriv At p  ad8317175eea: P2 M Fried Crossing Regularity has Deriv At p  ad8317175eea
-- statement:
--   The P2 M Fried Crossing Regularity has Deriv At p  ad8317175eea construction uses the P2 M Fried Crossing Regularity has Deriv At p  ad8317175eea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L160-L162
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L160-L162

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Regularity

theorem P2M_FriedCrossing_Regularity_hasDerivAt_p__ad8317175eea {f : ℝ → ℝ → ℝ} (hf : Differentiable ℝ fun q : ℝ × ℝ => f q.1 q.2)
    (θ τ : ℝ) : HasDerivAt (fun t => f θ t) (pτ f θ τ) τ := by sorry

alias «FriedCrossing».«Regularity».«hasDerivAt_pτ» := P2M_FriedCrossing_Regularity_hasDerivAt_p__ad8317175eea
