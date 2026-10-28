-- Prove2me | Theorems.Thm_ProbabilityTheory_bddBelow_setOf_le_cdf
-- name    : ProbabilityTheory.bddBelow_setOf_le_cdf
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T00:30:36.802895+00:00
-- url     : https://prove2.me/theorems/23b8fecd-3f99-4bdc-b29b-18d3c6a39210
-- title:
--   The upper level sets of a cdf are bounded below
-- statement:
--   Let $P$ be a probability measure on $\mathbb{R}$ with distribution function
--   $F_P(t) = P((-\infty, t])$, and let $u > 0$. Then the upper level set
--
--   $$
--   \{\, x \in \mathbb{R} \;:\; u \le F_P(x) \,\}
--   $$
--
--   is bounded below.
--
--   Together with the companion statement that this set is nonempty for $u < 1$, this is exactly
--   what makes the quantile
--
--   $$
--   q_P(u) \;=\; \inf\{\, x \;:\; u \le F_P(x) \,\}
--   $$
--
--   a well-defined real number rather than $-\infty$. Any argument that treats a quantile as a
--   number — a value-at-risk, a newsvendor order quantity, a critical fractile — needs
--   this boundedness first, and the hypothesis $u > 0$ cannot be dropped.
-- source:
--   P. Billingsley, Probability and Measure, 3rd ed., Wiley 1995, §14 (limits of a distribution function at $\pm\infty$); carved from the accepted proof of DualSSD.Duality.ssd_iff_secondQuantile_ge, https://prove2.me/submissions/24af3a16-a50a-4c61-a8f1-d10c467ef9d4

import Mathlib

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology

theorem ProbabilityTheory.bddBelow_setOf_le_cdf (P : Measure ℝ) [IsProbabilityMeasure P] {u : ℝ} (hu0 : 0 < u) :
    BddBelow {x | u ≤ cdf P x} := by sorry
