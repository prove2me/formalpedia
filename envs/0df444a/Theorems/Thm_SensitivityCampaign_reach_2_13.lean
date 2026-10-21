-- Prove2me | Theorems.Thm_SensitivityCampaign_reach_2_13
-- name    : SensitivityCampaign.reach_2_13
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T07:57:22.59192+00:00
-- url     : https://prove2.me/theorems/2efb73d4-3f84-4533-b0d8-454e4c89ed5e
-- title:
--   Separation exponent at least 2.13
-- statement:
--   For every epsilon > 0 and every integer S ≥ 2, some total Boolean function f satisfies s(f) ≥ S and bs(f) ≥ s(f)^(2.13−epsilon).
-- source:
--   https://github.com/bigospeedrun/site/issues/2

import Mathlib
import Definitions.Def_SensitivityCampaign
import Theorems.Thm_SensitivityCampaign_finite_certificate
import Theorems.Thm_SensitivityCampaign_finite_certificate_log
open OAI.Paper320

theorem SensitivityCampaign.reach_2_13 :
    SensitivityCampaign.AchievesExponent (2.13 : ℝ) := by sorry
