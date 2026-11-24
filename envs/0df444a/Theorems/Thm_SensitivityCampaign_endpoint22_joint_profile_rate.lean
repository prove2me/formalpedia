-- Prove2me | Theorems.Thm_SensitivityCampaign_endpoint22_joint_profile_rate
-- name    : SensitivityCampaign.endpoint22_joint_profile_rate
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-24T11:52:40.752426+00:00
-- url     : https://prove2.me/theorems/cec12ff2-f6f8-4755-9f30-2801db014420
-- title:
--   A sharper four-stage separation from the phase-two joint cover
-- statement:
--   Total Boolean functions attain the sensitivity versus block-sensitivity exponent $\log(5591^4)/\log(7211267676808970194/712440234061)$. The denominator inside the logarithm improves the four-stage reset using a joint flip estimate propagated from the preceding phase.
-- source:
--   The exact-rate proof https://prove2.me/theorems/dd747d44-9471-4892-8f1e-6899343d5552 and the accepted phase-two joint-cover proof https://prove2.me/submissions/6dc1fd9c-4370-4ac3-aacf-7ca773805531 are used for the same explicit family. The final transfer uses ThreeBoundMinmaxNumeric.dCore_bound.

import Definitions.Def_SensitivityCampaign

theorem SensitivityCampaign.endpoint22_joint_profile_rate : SensitivityCampaign.AchievesExponent
    (Real.log ((5591 : ℝ) ^ 4) / Real.log ((7211267676808970194 : ℝ) / 712440234061)) := by sorry
