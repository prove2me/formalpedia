-- Prove2me | Theorems.Thm_ThreeSum_TernaryPrincipalDimensions_incidence_slope_pos
-- name    : ThreeSum.TernaryPrincipalDimensions.incidence_slope_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:00:18.792346+00:00
-- url     : https://prove2.me/theorems/0828976f-e5e2-43e5-a3d8-4c26be8f0cc3
-- title:
--   Ternary Principal Dimensions: incidence slope pos
-- statement:
--   The Ternary Principal Dimensions construction uses the incidence slope pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPrincipalDimensions.lean#L116-L120
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPrincipalDimensions.lean#L116-L120

import Definitions.Def_Submission_ThreeSum_TernaryFiniteLedger
import Definitions.Def_Submission_ThreeSum_TernaryPrincipalDimensions
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPrincipalDimensions
open Real TernaryParameters TernaryEntropyRates TernaryDimensionBounds
open TernaryCoverScale TernaryLocalParameters TernaryFiniteLedger

theorem ThreeSum.TernaryPrincipalDimensions.incidence_slope_pos {m : ℕ} (hm : 0 < m) (hs : primeRate m < outputRate m) :
    0 < incidenceSlope m := by sorry
