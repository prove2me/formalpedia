-- Prove2me | Theorems.Thm_ThreeSum_TernaryPrincipalDimensions_bank_charge_eq
-- name    : ThreeSum.TernaryPrincipalDimensions.bank_charge_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:54:07.551666+00:00
-- url     : https://prove2.me/theorems/7170dc96-a0a3-4f82-b71a-9a691a41398d
-- title:
--   Ternary Principal Dimensions: bank charge eq
-- statement:
--   The Ternary Principal Dimensions construction uses the bank charge eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPrincipalDimensions.lean#L61-L64
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPrincipalDimensions.lean#L61-L64

import Definitions.Def_Submission_ThreeSum_TernaryFiniteLedger
import Definitions.Def_Submission_ThreeSum_TernaryPrincipalDimensions
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPrincipalDimensions
open Real TernaryParameters TernaryEntropyRates TernaryDimensionBounds
open TernaryCoverScale TernaryLocalParameters TernaryFiniteLedger

theorem ThreeSum.TernaryPrincipalDimensions.bank_charge_eq {m : ℕ} (hm : 0 < m) :
    2*((fixedLength m : ℝ)*Real.log 2*bankEntropy)/Real.log (outputSize m : ℝ)=bankCharge m := by sorry
