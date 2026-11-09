-- Prove2me | Theorems.Thm_TusnadyPlane_RandomPoints_lemma_2_3
-- name    : TusnadyPlane.RandomPoints.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:28:51.999668+00:00
-- url     : https://prove2.me/theorems/8d529883-950c-49eb-9609-a8b0bef3f6ad
-- title:
--   Lemma 2.3 — Local gain
-- statement:
--   Fix the local experiment: $n\ge1$ labeled points with fixed colors, distinct real heights, and fixed categories relative to a horizontal interval. Divide a nonempty vertical interval $J$ into $b\ge3$ equal ordered blocks, and independently assign inside-category points to uniform horizontal children. Write $a$ for the old endpoint function, $a_k$ for the child endpoint functions, and $m_R$ for the number of inside points in the inner vertical blocks. Then
--   $$\mathbb E\sum_{k=1}^b\operatorname{osc}_J a_k\ge\sum_{\ell=1}^b\operatorname{osc}_{B_\ell}a+\frac14\sqrt{m_R}.$$
--   The expectation averages the entire child experiment, including $m_R=0$; no favorable assignment is selected. This is the local ingredient for the conditional gain across all comparison rectangles.
--
--   Differences from the source:
--   - encoding: fixed heights, colors, positions relative to I, and independent uniform child indices → LocalData categories 0/1/2 and the normalized sum over (Fin n → Fin b); reason: the source explicitly says the functions depend only on this data; outside-point child indices have no effect and integrate out
--   - generalization: fixed local data from unit-square samples with distinct heights and no base-b rational coordinates → arbitrary real heights and categories with injective heights, without any boundary-avoidance requirement; reason: every source local configuration supplies such data and the same weights and inner counts; only height comparisons enter the functions, and a jump at an inner-block boundary is absent from the bottom block and present on the top block under the half-open convention
-- source:
--   Zhewei Wei, Tight Bounds for Tusnády’s Problem in the Plane, STOC 2027 submission #313 (October 2026), printed p. 6 (PDF p. 7), Lemma 2.3; local experiment §2.3

import Mathlib
import Definitions.Def_TusnadyPlane_RandomPoints_localExperiment
open MeasureTheory ProbabilityTheory

namespace TusnadyPlane.RandomPoints

/-- Lemma 2.3, printed p.6 / PDF p.7, with the fixed data of §2.3. -/
theorem lemma_2_3 (n b : ℕ) (hn : 1 ≤ n) (hb : 3 ≤ b)
    (lo hi : ℝ) (hJ : lo < hi) (d : LocalData n) (hd : Function.Injective d.height) :
    (∑ l : Fin b, oscillation (block lo hi b l.val) (oldFunction d)) +
      (1/4 : ℝ) * Real.sqrt (localInnerCount d lo hi b) ≤
        localExpectedOscillation d lo hi b := by sorry

end TusnadyPlane.RandomPoints
