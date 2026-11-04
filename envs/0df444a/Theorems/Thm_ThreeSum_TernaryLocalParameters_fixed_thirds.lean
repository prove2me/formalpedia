-- Prove2me | Theorems.Thm_ThreeSum_TernaryLocalParameters_fixed_thirds
-- name    : ThreeSum.TernaryLocalParameters.fixed_thirds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:47:33.730244+00:00
-- url     : https://prove2.me/theorems/022e09cc-e3dc-4944-8990-13a713add116
-- title:
--   Ternary Local Parameters: fixed thirds
-- statement:
--   The Ternary Local Parameters construction uses the fixed thirds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryLocalParameters.lean#L21-L23
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryLocalParameters.lean#L21-L23

import Definitions.Def_Submission_ThreeSum_TernaryCoverUniformProjection
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryLocalParameters
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryLocalParameters
open Finset TernaryJointType TernaryCoverLocal TernaryTypeLowerBound TernaryCoverUniformProjection

theorem ThreeSum.TernaryLocalParameters.fixed_thirds (m : ℕ) : fixedPi m 2 = 3*(fixedAlpha m 2) := by sorry
