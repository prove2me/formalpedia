-- Prove2me | Theorems.Thm_ThreeSum_TernaryPrincipalDimensions_incidence_charge_eq
-- name    : ThreeSum.TernaryPrincipalDimensions.incidence_charge_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:54:11.812465+00:00
-- url     : https://prove2.me/theorems/1879cb05-48d6-41bf-a2d3-b3a8ab0457b1
-- title:
--   Ternary Principal Dimensions: incidence charge eq
-- statement:
--   The Ternary Principal Dimensions construction uses the incidence charge eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPrincipalDimensions.lean#L134-L138
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPrincipalDimensions.lean#L134-L138

import Definitions.Def_Submission_ThreeSum_TernaryFiniteLedger
import Definitions.Def_Submission_ThreeSum_TernaryPrincipalDimensions
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPrincipalDimensions
open Real TernaryParameters TernaryEntropyRates TernaryDimensionBounds
open TernaryCoverScale TernaryLocalParameters TernaryFiniteLedger

theorem ThreeSum.TernaryPrincipalDimensions.incidence_charge_eq {m : ℕ} (hm : 0 < m) :
    1+2*incidenceSlope m/Real.log (outputSize m : ℝ)=incidenceCharge m := by sorry
