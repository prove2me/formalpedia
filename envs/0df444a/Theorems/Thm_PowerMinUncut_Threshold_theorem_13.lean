-- Prove2me | Theorems.Thm_PowerMinUncut_Threshold_theorem_13
-- name    : PowerMinUncut.Threshold.theorem_13
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:44:58.699479+00:00
-- url     : https://prove2.me/theorems/c13013ef-a5af-4b2f-ae40-eb96706d4635
-- title:
--   Theorem 13 — UGC-conditional hardness: every factor A < C_{k,q} (k > q), and every finite A (2 ≤ k ≤ q), has an NP-hard promise gap
-- statement:
--   Assume the Unique Games Conjecture, and let $q\ge2$ and $k\ge2$ be integers. If $k>q$, every approximation factor strictly smaller than $C_{k,q}$ is NP-hard in the following promise sense: for every such factor $A\ge1$ there are fixed positive rational thresholds $c<s$ with $s/c>A$ for which distinguishing
--   $$\mathrm{OPT}_{k,q}(G)\le c\qquad\text{from}\qquad \mathrm{OPT}_{k,q}(G)\ge s$$
--   is NP-hard, on graphs with nonnegative rational weights of total one. If $2\le k\le q$, the same conclusion holds for every fixed finite factor $A\ge1$.
--
--   Differences from the source:
--   - encoding: Unique Games Conjecture → `OptInapprox.MaxCut.UGC` (platform definition: Khot's conjecture for bipartite Unique Label Cover); reason: the paper's weighted formulation (Isaksson–Mossel) is implied by it; unweighted instances are weighted instances
--   - encoding: distinguishing … is NP-hard → `PromiseNPHard k q c s` = `GapNPHard encGraph` with YES: total one ∧ OPT ≤ c, NO: total one ∧ OPT ≥ s; reason: Cook-model polynomial-time many-one reductions from every NP language; binary encoding of weights
-- source:
--   Xie, Sharp Power Loss Thresholds for Vector Min Uncut, STOC 2027 submission (manuscript sha256 391063da…), pp. 49–50, §10, Theorem 13

import Mathlib
import Definitions.Def_PowerMinUncut_Threshold_Machine

open MeasureTheory ProbabilityTheory Filter Topology

namespace PowerMinUncut.Threshold

open WGraph

/-- **Theorem 13 (conditional hardness)**, pp. 49–50. Assume the Unique Games Conjecture, and let
`q ≥ 2`, `k ≥ 2` be integers. If `k > q`, for every factor `1 ≤ A < C_{k,q}` there are fixed positive
rational thresholds `c < s` with `s/c > A` for which distinguishing `OPT_{k,q}(G) ≤ c` from
`OPT_{k,q}(G) ≥ s` (graphs with nonnegative rational weights of total one) is NP-hard. If
`2 ≤ k ≤ q`, the same holds for every finite factor `A ≥ 1`. -/
theorem theorem_13 (q k : ℕ) (hq : 2 ≤ q) (hk : 2 ≤ k) (hUGC : OptInapprox.MaxCut.UGC) :
    (q < k → ∀ A : ℝ, 1 ≤ A → A < Ckp k q →
      ∃ c s : ℚ, 0 < c ∧ c < s ∧ A < (s : ℝ) / (c : ℝ) ∧ PromiseNPHard k q c s) ∧
    (k ≤ q → ∀ A : ℝ, 1 ≤ A →
      ∃ c s : ℚ, 0 < c ∧ c < s ∧ A < (s : ℝ) / (c : ℝ) ∧ PromiseNPHard k q c s) := by sorry

end PowerMinUncut.Threshold
