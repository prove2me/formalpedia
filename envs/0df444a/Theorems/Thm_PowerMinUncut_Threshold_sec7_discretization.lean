-- Prove2me | Theorems.Thm_PowerMinUncut_Threshold_sec7_discretization
-- name    : PowerMinUncut.Threshold.sec7_discretization
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:43:53.227438+00:00
-- url     : https://prove2.me/theorems/d3420d32-02f0-487c-846c-6ae6c248000f
-- title:
--   §7 — finite rational graphs attain the gap: ratio ≥ (C_{k,q} − η)/(1 + η) for k > q, unbounded for k ≤ q
-- statement:
--   Let $q\ge2$ be an integer.
--   1. If $k>q$, for every $\eta>0$ there is a finite loopless graph $G$ with nonnegative rational weights of total one, $\mathrm{REL}_q(G)>0$ and
--   $$\frac{\mathrm{OPT}_{k,q}(G)}{\mathrm{REL}_q(G)}\ \ge\ \frac{C_{k,q}-\eta}{1+\eta}.$$
--   2. If $1\le k\le q$, such graphs have arbitrarily large ratios: for every $B$ some $G$ has $\mathrm{REL}_q(G)>0$ and $\mathrm{OPT}_{k,q}(G)/\mathrm{REL}_q(G)\ge B$.
--
--   The graphs are discretizations of a near-antipodal edge measure on a sphere; together with the upper bound this proves the gap clause of Theorem 1.
--
--   Differences from the source:
--   - encoding: arbitrarily large ratios → for every real B some graph has ratio ≥ B; reason: the same statement
--   - encoding: finite rational weighted loopless graph → `WGraph` on `Fin N` with a symmetric nonnegative ℚ weight function, zero diagonal; edges are pairs i < j, each counted once; reason: Lean representation; zero-weight pairs contribute nothing
-- source:
--   Xie, Sharp Power Loss Thresholds for Vector Min Uncut, STOC 2027 submission (manuscript sha256 391063da…), p. 34, §7

import Mathlib
import Definitions.Def_PowerMinUncut_Threshold_Instance

open MeasureTheory ProbabilityTheory Filter Topology

namespace PowerMinUncut.Threshold

open WGraph

/-- **§7, finite rational graphs attain the gap**, p. 34. For an integer `q ≥ 2`: if `k > q`, for
every `η > 0` some finite loopless graph with nonnegative rational weights of total one has
`REL_q(G) > 0` and `OPT_{k,q}(G)/REL_q(G) ≥ (C_{k,q} - η)/(1 + η)`; if `1 ≤ k ≤ q`, such graphs have
arbitrarily large ratios. -/
theorem sec7_discretization (q : ℕ) (hq : 2 ≤ q) :
    (∀ k : ℕ, q < k → ∀ η : ℝ, 0 < η → ∃ G : WGraph, G.total = 1 ∧ 0 < WGraph.REL q G ∧
      (Ckp k q - η) / (1 + η) ≤ WGraph.OPT k q G / WGraph.REL q G) ∧
    (∀ k : ℕ, 1 ≤ k → k ≤ q → ∀ B : ℝ, ∃ G : WGraph, G.total = 1 ∧ 0 < WGraph.REL q G ∧
      B ≤ WGraph.OPT k q G / WGraph.REL q G) := by sorry

end PowerMinUncut.Threshold
