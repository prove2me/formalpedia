-- Prove2me | Theorems.Thm_PowerMinUncut_Threshold_theorem_7
-- name    : PowerMinUncut.Threshold.theorem_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:43:52.242494+00:00
-- url     : https://prove2.me/theorems/a46e5dec-2017-4de9-beaa-26bfacbc4412
-- title:
--   Theorem 7 — normalized Gaussian projection: E‖Gu/‖Gu‖ − Gv/‖Gv‖‖^p ≤ C_{k,p}‖u − v‖^p, sharp for every N ≥ 2, constant one for N = 1
-- statement:
--   Let $p\ge1$ be real, $k>p$ an integer, and $G$ a standard Gaussian $k\times N$ matrix, $N\ge1$. For unit $u,v\in\mathbb R^N$,
--   $$\mathbb E\left\|\frac{Gu}{\|Gu\|}-\frac{Gv}{\|Gv\|}\right\|^p\le C_{k,p}\,\|u-v\|^p,\qquad C_{k,p}=\frac{\Gamma((k-1+p)/2)\Gamma((k-p)/2)}{\Gamma((k-1)/2)\Gamma(k/2)}.$$
--   The constant is sharp uniformly in the dimension and for each fixed $N\ge2$: the least upper bound of the ratios $\mathbb E\|\cdot\|^p/\|u-v\|^p$ over unit $u\neq v$ is $C_{k,p}$. For $N=1$ the optimal constant is one.
--
--   This is the global rounding inequality; applied to $u_i,-u_j$ it gives the upper bound $\mathrm{OPT}_{k,q}\le C_{k,q}\mathrm{REL}_q$.
--
--   Differences from the source:
--   - encoding: the constant is sharp for each fixed N ≥ 2; for N = 1 the optimal constant is one → IsLUB of the set of ratios E‖·‖^p/‖u − v‖^p over unit u ≠ v (equal to C_{k,p} for N ≥ 2, to 1 for N = 1); reason: the optimal constant is the supremum of these ratios, as u = v gives 0 ≤ 0
--   - encoding: standard Gaussian k × N matrix → product of standard real Gaussians on Fin k → Fin N → ℝ; reason: Lean representation
-- source:
--   Xie, Sharp Power Loss Thresholds for Vector Min Uncut, STOC 2027 submission (manuscript sha256 391063da…), p. 9, Theorem 7, (E3)

import Mathlib
import Definitions.Def_PowerMinUncut_Threshold_Instance
import Definitions.Def_PowerMinUncut_Threshold_Gaussian

open MeasureTheory ProbabilityTheory Filter Topology

namespace PowerMinUncut.Threshold

open WGraph

/-- **Theorem 7 (real power Gaussian projection)**, p. 9. For real `p ≥ 1`, an integer `k > p`, a
standard Gaussian `k × N` matrix `G` (`N ≥ 1`) and unit `u, v ∈ ℝ^N`:
`E‖Gu/‖Gu‖ - Gv/‖Gv‖‖^p ≤ C_{k,p} ‖u - v‖^p` (E3). The constant is sharp uniformly in the dimension
and for each fixed `N ≥ 2` (the least upper bound of the ratios over unit `u ≠ v` is `C_{k,p}`);
for `N = 1` the optimal constant is one. -/
theorem theorem_7 (p : ℝ) (hp : 1 ≤ p) (k : ℕ) (hk : p < k) :
    (∀ N : ℕ, 1 ≤ N → ∀ u v : E N, ‖u‖ = 1 → ‖v‖ = 1 →
      projMoment k N p u v ≤ Ckp k p * ‖u - v‖ ^ p) ∧
    (∀ N : ℕ, 2 ≤ N → IsLUB {r : ℝ | ∃ u v : E N, ‖u‖ = 1 ∧ ‖v‖ = 1 ∧ u ≠ v ∧
      r = projMoment k N p u v / ‖u - v‖ ^ p} (Ckp k p)) ∧
    IsLUB {r : ℝ | ∃ u v : E 1, ‖u‖ = 1 ∧ ‖v‖ = 1 ∧ u ≠ v ∧
      r = projMoment k 1 p u v / ‖u - v‖ ^ p} 1 := by sorry

end PowerMinUncut.Threshold
