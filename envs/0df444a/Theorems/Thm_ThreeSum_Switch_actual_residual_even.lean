-- Prove2me | Theorems.Thm_ThreeSum_Switch_actual_residual_even
-- name    : ThreeSum.Switch.actual_residual_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:03:10.4016+00:00
-- url     : https://prove2.me/theorems/34f9ea46-6353-4fee-81c9-b3ee637b0547
-- title:
--   Switch: actual residual even
-- statement:
--   The Switch construction uses the actual residual even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Switch.lean#L190-L191
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Switch.lean#L190-L191

import Definitions.Def_Submission_ThreeSum_BandScales
import Mathlib.Data.Finset.Max
import Definitions.Def_Submission_ThreeSum_Switch
set_option autoImplicit false
open ThreeSum ThreeSum.Switch
open Set ThreeSum.Parameters ThreeSum.Scales
set_option maxHeartbeats 0
noncomputable section

theorem ThreeSum.Switch.actual_residual_even (n j : ℕ) : 2 ∣ residualSize n j := by sorry
