-- Prove2me | Theorems.Thm_PowerMinUncut_Threshold_eq_11
-- name    : PowerMinUncut.Threshold.eq_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:44:06.724798+00:00
-- url     : https://prove2.me/theorems/753251b4-7432-4a0f-8514-7edc0b847217
-- title:
--   §7, Eq. (11) — REL_q(G) = 0 iff the support is bipartite; otherwise REL_q(G) ≥ 2^q w_min/N^{q−1} > 0
-- statement:
--   Let $q\ge2$ be an integer and $G$ a finite loopless graph on $N$ vertices with nonnegative rational weights. The positive-weight support is bipartite if and only if $\mathrm{REL}_q(G)=0$. If it is not bipartite and $w_{\min}$ is the smallest positive edge weight, then
--   $$\mathrm{REL}_q(G)\ \ge\ \frac{2^q\,w_{\min}}{N^{q-1}}\ >\ 0.\tag{11}$$
--   This bound makes every precision of the rounding algorithm logarithmic in the reciprocal optimum.
--
--   Differences from the source:
--   - generalization: weights of total one (standing assumption, p. 1) → any nonnegative rational weights; reason: the proof never uses the normalization; total one is the special case
--   - encoding: w_min the smallest positive edge weight → a rational wmin that is the weight of some positive-weight pair and at most every positive weight; reason: the definition of the smallest positive weight
--   - encoding: finite rational weighted loopless graph → `WGraph` on `Fin N` with a symmetric nonnegative ℚ weight function, zero diagonal; edges are pairs i < j, each counted once; reason: Lean representation; zero-weight pairs contribute nothing
-- source:
--   Xie, Sharp Power Loss Thresholds for Vector Min Uncut, STOC 2027 submission (manuscript sha256 391063da…), p. 34, §7, Eq. (11)

import Mathlib
import Definitions.Def_PowerMinUncut_Threshold_Instance

open MeasureTheory ProbabilityTheory Filter Topology

namespace PowerMinUncut.Threshold

open WGraph

/-- **§7, Eq. (11)**, p. 34. For an integer `q ≥ 2` and a finite loopless graph on `N` vertices with
nonnegative rational weights: `REL_q(G) = 0` if and only if the positive-weight support is
bipartite; otherwise, with `w_min` the smallest positive edge weight,
`REL_q(G) ≥ 2^q w_min / N^{q-1} > 0`. -/
theorem eq_11 (q : ℕ) (hq : 2 ≤ q) (G : WGraph) :
    (WGraph.REL q G = 0 ↔ G.SupportBipartite) ∧
    (¬ G.SupportBipartite → ∀ wmin : ℚ, (∃ i j, 0 < G.w i j ∧ G.w i j = wmin) →
      (∀ i j, 0 < G.w i j → wmin ≤ G.w i j) →
      0 < 2 ^ q * (wmin : ℝ) / (G.N : ℝ) ^ (q - 1) ∧
        2 ^ q * (wmin : ℝ) / (G.N : ℝ) ^ (q - 1) ≤ WGraph.REL q G) := by sorry

end PowerMinUncut.Threshold
