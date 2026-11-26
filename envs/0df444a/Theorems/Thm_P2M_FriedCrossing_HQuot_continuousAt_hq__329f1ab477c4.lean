-- Prove2me | Theorems.Thm_P2M_FriedCrossing_HQuot_continuousAt_hq__329f1ab477c4
-- name    : P2M_FriedCrossing_HQuot_continuousAt_hq__329f1ab477c4
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T04:49:34.390596+00:00
-- url     : https://prove2.me/theorems/d8864e08-e539-5c63-8a6b-034663d3aa4c
-- title:
--   P2 M Fried Crossing HQuot continuous At hq  329f1ab477c4: P2 M Fried Crossing HQuot continuous At hq  329f1ab477c4
-- statement:
--   Joint continuity at (0,0) of the derivative of the Hadamard quotient of a parametrised
--   family, from joint continuity of the second derivative.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L311-L356
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L311-L356

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.HQuot

theorem P2M_FriedCrossing_HQuot_continuousAt_hq__329f1ab477c4 {F F' F'' : ℝ → ℝ → ℝ}
    (hF : ∀ θ t, HasDerivAt (F θ) (F' θ t) t) (hF' : ∀ θ t, HasDerivAt (F' θ) (F'' θ t) t)
    (hc : ContinuousAt (fun q : ℝ × ℝ => F'' q.1 q.2) (0, 0)) :
    ContinuousAt (fun p : ℝ × ℝ => hq' (F p.1) (F' p.1) (F'' p.1) p.2) (0, 0) := by sorry

alias «FriedCrossing».«HQuot».«continuousAt_hq'» := P2M_FriedCrossing_HQuot_continuousAt_hq__329f1ab477c4
