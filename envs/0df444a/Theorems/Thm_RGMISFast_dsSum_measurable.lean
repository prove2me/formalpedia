-- Prove2me | Theorems.Thm_RGMISFast_dsSum_measurable
-- name    : RGMISFast.dsSum_measurable
-- status  : Proved
-- author  : @srikkanthr
-- created : 2026-11-16T01:07:31.154737+00:00
-- url     : https://prove2.me/theorems/887a94f7-e862-4d54-93d3-7adb7d0d9752
-- title:
--   Measurability of the active-set destruction-rate sum
-- statement:
--   For every finite graph, fixed root $u$, size $k$, and time $s$, the finite count $\sum_W d_s(W)$ is measurable as a function of the ranks. The sum ranges over $k$-sets $W$ for which $\{u\}\cup W$ is root-connected and active at $s$; $d_s(W)$ is computed in the graph active at $s$. This is the second measurability clause of Equation (20), stated independently of a probability law.
-- source:
--   Dalirrooyfard, Makarychev, Mitrović, Ramachandran, Randomized Greedy MIS Is Fast at Every Node, §5.1, proof of Lemma 5.2, printed pp.18–19 (PDF pp.20–21), polynomial-in-exp(-s) observation and the short-window destruction calculation yielding Equation (20). Auxiliary finite exponential-basis reformulation.

import Mathlib
import Definitions.Def_RGMISFast_Y
import Definitions.Def_RGMISFast_condLaw

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open RGMISFast

theorem RGMISFast.dsSum_measurable {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (k : ℕ) (s : ℝ) :
    Measurable (fun r : V → ℝ => dsSum G u k s r) := by sorry
