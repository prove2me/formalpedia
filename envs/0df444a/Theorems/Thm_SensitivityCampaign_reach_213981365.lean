-- Prove2me | Theorems.Thm_SensitivityCampaign_reach_213981365
-- name    : SensitivityCampaign.reach_213981365
-- status  : Proved
-- author  : @dmilosch
-- created : 2026-11-06T23:38:12.66598+00:00
-- url     : https://prove2.me/theorems/ef444210-5a67-4f94-8c62-6387466defdd
-- title:
--   The existing twenty-two-level construction achieves exponent 2.13981365
-- statement:
--   The sensitivity versus block-sensitivity separation holds at the exact exponent
--
--   $$\beta=\frac{213981365}{100000000}=2.13981365.$$
--
--   For every positive real number $\varepsilon$ and every integer threshold $S\ge2$, there are a natural number $n$ and a total Boolean function $f:\{0,1\}^n\to\{0,1\}$ such that
--
--   $$s(f)\ge S,\qquad \operatorname{bs}(f)\ge s(f)^{\beta-\varepsilon}.$$
--
--   This sharpens the published exponent 2.13981 extracted from the existing twenty-two-level seed family. It uses that family's already proved sensitivity growth bound $10^{15}10121928^m$ and block-sensitivity growth bound $(5591^4)^m$. It introduces no new graph, labeling, profile recurrence, or seed construction.
-- source:
--   Numerical sharpening of the already Proved theorem Sensitivity213981.actual_seeds, https://prove2.me/theorems/e4a62ddd-b529-418d-98c1-9e04556d9a83, whose exact seed bounds are s(f_m)<=10^15*10121928^m and bs(f_m)>=(5591^4)^m. The previously published endpoint is SensitivityCampaign.reach_213981, https://prove2.me/theorems/0e93b146-3cac-42d3-b8f4-74010d06b636. The asymptotic passage uses the Proved SensitivityCampaign.finite_certificate, https://prove2.me/theorems/06deb432-c715-4a68-b79d-3078b3bc9a09. The new arithmetic certificate is 10121928^37665 < 5591^70408, verified in the Lean kernel. The logarithmic overhead argument adapts SensitivityProfileCycleGrowth.achieves_strict in the existing workspace, retaining its attribution to submission a9d25c46-43bd-4fb1-826b-0ed075b8cf0a by yousofy with Codex and the underlying community construction.

import Definitions.Def_SensitivityCampaign

theorem SensitivityCampaign.reach_213981365 :
    SensitivityCampaign.AchievesExponent (213981365 / 100000000 : ℝ) := by sorry
