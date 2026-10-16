-- Prove2me | Theorems.Thm_SensitivityCampaign_baseline_arithmetic
-- name    : SensitivityCampaign.baseline_arithmetic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-15T17:43:57.976327+00:00
-- url     : https://prove2.me/theorems/afb26e48-a36c-478b-9767-f87081453d9a
-- title:
--   Certified exponent 2.000252407 for the depth-9 seed
-- statement:
--   With $M=9^{10}$, $A=2(9+2)M^{10}$, and $B=M^2(2M^2+1)^{9}$, prove the exact real inequality $A^{2.000252407}\le B$. The decimal denotes an exact rational real value, not a floating-point approximation.
-- source:
--   https://github.com/bigospeedrun/site/issues/2

import Mathlib
import Definitions.Def_SensitivityCampaign
open OAI.Paper320

theorem SensitivityCampaign.baseline_arithmetic :
    let M : ℕ := 9 ^ 10
    ((2 * (9 + 2) * M ^ 10 : ℕ) : ℝ) ^ (2.000252407 : ℝ) ≤
      ((M ^ 2 * (2 * M ^ 2 + 1) ^ 9 : ℕ) : ℝ) := by sorry
