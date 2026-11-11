-- Prove2me | Theorems.Thm_PowerMinUncut_Threshold_sec10_11
-- name    : PowerMinUncut.Threshold.sec10_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:44:50.514631+00:00
-- url     : https://prove2.me/theorems/26f06837-74a4-4878-9796-b746c7e038c8
-- title:
--   §10.11 — rank-one hardness: OPT_{1,q} = 2^q · Min Uncut and, under UGC, every finite factor has an NP-hard promise gap
-- statement:
--   Let $q\ge2$ be an integer. When $k=1$ every vector belongs to $S^0=\{-1,+1\}$ and $|z_v+z_w|^q$ is $0$ if $z_v\neq z_w$ and $2^q$ if $z_v=z_w$, so
--   $$\mathrm{OPT}_{1,q}(G)=2^q\cdot\mathrm{MinUncut}(G),$$
--   the weighted Min Uncut value, with every approximation ratio unchanged. Assuming the Unique Games Conjecture (via the Max-Cut gap of Khot, Kindler, Mossel and O'Donnell), for every finite factor $A\ge1$ there are fixed thresholds $0<c<s$ with $s/c>A$ for which distinguishing $\mathrm{OPT}_{1,q}(G)\le c$ from $\mathrm{OPT}_{1,q}(G)\ge s$ is NP-hard.
--
--   Differences from the source:
--   - generalization: thresholds 2^qη versus 2^q(2/π)√η (positive reals) → rational thresholds c < s; reason: a rational pair strictly inside the real promise gives the same hardness; rational thresholds imply the real statement
--   - encoding: Unique Games Conjecture; NP-hard promise → `OptInapprox.MaxCut.UGC`; `PromiseNPHard 1 q c s`; reason: as in Theorem 13
--   - encoding: finite rational weighted loopless graph → `WGraph` on `Fin N` with a symmetric nonnegative ℚ weight function, zero diagonal; edges are pairs i < j, each counted once; reason: Lean representation; zero-weight pairs contribute nothing
-- source:
--   Xie, Sharp Power Loss Thresholds for Vector Min Uncut, STOC 2027 submission (manuscript sha256 391063da…), p. 63, §10.11

import Mathlib
import Definitions.Def_PowerMinUncut_Threshold_Machine

open MeasureTheory ProbabilityTheory Filter Topology

namespace PowerMinUncut.Threshold

open WGraph

/-- **§10.11, rank-one hardness**, p. 63. For every integer `q ≥ 2`, `OPT_{1,q}(G)` is exactly `2^q`
times ordinary (weighted) Min Uncut; and, assuming the Unique Games Conjecture, for every finite
factor `A ≥ 1` there are fixed positive thresholds `c < s` with `s/c > A` such that distinguishing
`OPT_{1,q}(G) ≤ c` from `OPT_{1,q}(G) ≥ s` is NP-hard. -/
theorem sec10_11 (q : ℕ) (hq : 2 ≤ q) :
    (∀ G : WGraph, WGraph.OPT 1 q G = 2 ^ q * G.minUncut) ∧
    (OptInapprox.MaxCut.UGC → ∀ A : ℝ, 1 ≤ A →
      ∃ c s : ℚ, 0 < c ∧ c < s ∧ A < (s : ℝ) / (c : ℝ) ∧ PromiseNPHard 1 q c s) := by sorry

end PowerMinUncut.Threshold
