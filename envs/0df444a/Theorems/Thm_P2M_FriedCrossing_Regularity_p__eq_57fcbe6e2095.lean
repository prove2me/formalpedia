-- Prove2me | Theorems.Thm_P2M_FriedCrossing_Regularity_p__eq_57fcbe6e2095
-- name    : P2M_FriedCrossing_Regularity_p__eq_57fcbe6e2095
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:43:00.458714+00:00
-- url     : https://prove2.me/theorems/7dba64ac-ffd6-579f-a270-9955f6f503ca
-- title:
--   P2 M Fried Crossing Regularity p  eq 57fcbe6e2095: P2 M Fried Crossing Regularity p  eq 57fcbe6e2095
-- statement:
--   The P2 M Fried Crossing Regularity p  eq 57fcbe6e2095 construction uses the P2 M Fried Crossing Regularity p  eq 57fcbe6e2095 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L156-L158
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L156-L158

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Regularity

theorem P2M_FriedCrossing_Regularity_p__eq_57fcbe6e2095 {f : ℝ → ℝ → ℝ} (hf : Differentiable ℝ fun q : ℝ × ℝ => f q.1 q.2) (θ τ : ℝ) :
    pθ f θ τ = fderiv ℝ (fun q : ℝ × ℝ => f q.1 q.2) (θ, τ) (1, 0) := by sorry

alias «FriedCrossing».«Regularity».«pθ_eq» := P2M_FriedCrossing_Regularity_p__eq_57fcbe6e2095
