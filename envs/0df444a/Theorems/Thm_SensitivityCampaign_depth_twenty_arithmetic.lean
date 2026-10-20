-- Prove2me | Theorems.Thm_SensitivityCampaign_depth_twenty_arithmetic
-- name    : SensitivityCampaign.depth_twenty_arithmetic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-15T17:45:23.943973+00:00
-- url     : https://prove2.me/theorems/fb8ef2a6-9f9e-4097-80b0-622d2be88abf
-- title:
--   Certified exponent 2.006470828 for the depth-20 seed
-- statement:
--   With $M=9^{21}$, $A=2(20+2)M^{21}$, and $B=M^2(2M^2+1)^{20}$, prove the exact real inequality $A^{2.006470828}\le B$. The decimal denotes an exact rational real value, not a floating-point approximation.
-- source:
--   https://github.com/bigospeedrun/site/issues/2

import Mathlib
import Definitions.Def_SensitivityCampaign
open OAI.Paper320

theorem SensitivityCampaign.depth_twenty_arithmetic :
    let M : ℕ := 9 ^ 21
    ((2 * (20 + 2) * M ^ 21 : ℕ) : ℝ) ^ (2.006470828 : ℝ) ≤
      ((M ^ 2 * (2 * M ^ 2 + 1) ^ 20 : ℕ) : ℝ) := by sorry
