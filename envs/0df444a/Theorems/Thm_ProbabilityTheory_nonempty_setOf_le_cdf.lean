-- Prove2me | Theorems.Thm_ProbabilityTheory_nonempty_setOf_le_cdf
-- name    : ProbabilityTheory.nonempty_setOf_le_cdf
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T00:30:40.068305+00:00
-- url     : https://prove2.me/theorems/e3ee856d-f727-438c-85a2-7654bd8f9128
-- title:
--   The upper level sets of a cdf below 1 are nonempty
-- statement:
--   Let $P$ be a probability measure on $\mathbb{R}$ with distribution function
--   $F_P(t) = P((-\infty, t])$, and let $u < 1$. Then the upper level set
--
--   $$
--   \{\, x \in \mathbb{R} \;:\; u \le F_P(x) \,\}
--   $$
--
--   is nonempty.
--
--   This is the second half of what the quantile $q_P(u) = \inf\{x : u \le F_P(x)\}$ needs in order
--   to be a real number: the set it takes an infimum over must be both nonempty (this statement, for
--   $u < 1$) and bounded below (the companion statement, for $u > 0$). The two together cover every
--   level $u \in (0,1)$, which is the range on which quantiles, values-at-risk and critical
--   fractiles are used.
-- source:
--   P. Billingsley, Probability and Measure, 3rd ed., Wiley 1995, §14 (limits of a distribution function at $\pm\infty$); carved from the accepted proof of DualSSD.Duality.ssd_iff_secondQuantile_ge, https://prove2.me/submissions/24af3a16-a50a-4c61-a8f1-d10c467ef9d4

import Mathlib

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology

theorem ProbabilityTheory.nonempty_setOf_le_cdf (P : Measure ℝ) [IsProbabilityMeasure P] {u : ℝ} (hu1 : u < 1) :
    ({x | u ≤ cdf P x} : Set ℝ).Nonempty := by sorry
