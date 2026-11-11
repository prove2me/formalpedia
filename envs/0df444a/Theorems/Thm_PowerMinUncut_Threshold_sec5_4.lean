-- Prove2me | Theorems.Thm_PowerMinUncut_Threshold_sec5_4
-- name    : PowerMinUncut.Threshold.sec5_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:44:54.379215+00:00
-- url     : https://prove2.me/theorems/50b89861-9381-407c-9847-55bef8899bc6
-- title:
--   §5.4 — critical nonexistence of odd W^{1,q} maps S^d → S^{k−1} (k ≤ q) and divergence of the shell infimum
-- statement:
--   Let $q\ge2$ be an integer.
--   1. If $2\le k\le q$ and $d\ge k$, there is no odd map in $W^{1,q}(S^d;S^{k-1})$.
--   2. For $k=1$ there is no odd map in $W^{1,q}(S^d;S^0)$ on a connected sphere $S^d$, $d\ge1$ (such a map is constant).
--   3. For $1\le k\le q$ and $d\ge\max\{2,k\}$,
--   $$\inf_{F:S^d\to S^{k-1}}\frac{E_\theta(F)}{\theta^q}\longrightarrow\infty\qquad(\theta\downarrow0),$$
--   the infimum over measurable maps.
--
--   This is the critical half of the rank threshold: at or below the power, no odd finite-energy map exists, so the normalized endpoint diverges.
--
--   Differences from the source:
--   - reading: k = 1: constant on a connected sphere → k = 1 and d ≥ 1; reason: S^d is connected exactly for d ≥ 1
--   - encoding: odd W^{1,q}(S^d; S^{k−1}) → `IsOddSphereSobolev`; reason: as in Lemma 5
--   - encoding: the infimum diverges along every sequence of angles tending to zero → Tendsto (shellInf d k q) (𝓝[>] 0) atTop; reason: the same statement for the function of θ
--   - encoding: E_θ over measurable F : S^d → S^{k−1} → `shellInf`: the angle-θ pair built from two independent Gaussian vectors, over measurable F : ℝ^{d+1} → ℝ^k with ‖F(x)‖ = 1 on S^d; reason: as in Eq. (7): the pair has the rotation-invariant angle-θ law, and only values on S^d matter
-- source:
--   Xie, Sharp Power Loss Thresholds for Vector Min Uncut, STOC 2027 submission (manuscript sha256 391063da…), p. 15, §5.4

import Mathlib
import Definitions.Def_PowerMinUncut_Threshold_Sobolev

open MeasureTheory ProbabilityTheory Filter Topology

namespace PowerMinUncut.Threshold

/-- **§5.4, critical nonexistence and qualitative divergence**, p. 15. For an integer `q ≥ 2`:
if `2 ≤ k ≤ q` and `d ≥ k` there is no odd map in `W^{1,q}(S^d; S^{k-1})`; for `k = 1` there is no
odd map in `W^{1,q}(S^d; S^0)` on a (connected) sphere `S^d`, `d ≥ 1`; and for `1 ≤ k ≤ q` and
`d ≥ max{2, k}`, `inf_F E_θ(F)/θ^q → ∞` as `θ ↓ 0`. -/
theorem sec5_4 (q : ℕ) (hq : 2 ≤ q) :
    (∀ k d : ℕ, 2 ≤ k → k ≤ q → k ≤ d →
      ¬ ∃ (F : E (d + 1) → E k) (DF : E (d + 1) → (E (d + 1) →L[ℝ] E k)),
        IsOddSphereSobolev d q F DF) ∧
    (∀ d : ℕ, 1 ≤ d →
      ¬ ∃ (F : E (d + 1) → E 1) (DF : E (d + 1) → (E (d + 1) →L[ℝ] E 1)),
        IsOddSphereSobolev d q F DF) ∧
    (∀ k d : ℕ, 1 ≤ k → k ≤ q → 2 ≤ d → k ≤ d →
      Tendsto (shellInf d k q) (𝓝[>] (0 : ℝ)) atTop) := by sorry

end PowerMinUncut.Threshold
