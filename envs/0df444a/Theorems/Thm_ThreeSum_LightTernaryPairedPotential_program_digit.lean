-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryPairedPotential_program_digit
-- name    : ThreeSum.LightTernaryPairedPotential.program_digit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:49:10.129263+00:00
-- url     : https://prove2.me/theorems/fb45ef97-efc2-4072-b7ce-46034ab1eb12
-- title:
--   Light Ternary Paired Potential: program digit
-- statement:
--   The Light Ternary Paired Potential construction uses the program digit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPairedPotential.lean#L259-L259
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPairedPotential.lean#L259-L259

import Definitions.Def_Submission_ThreeSum_TernaryPairedColumnEnumeration
import Definitions.Def_Submission_ThreeSum_LightWeightRow
import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPotential
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryPairedPotential
open Light LightTernaryPairedPolynomial TernaryPairedColumnEnumeration TernaryPairedTensor
open scoped BigOperators

theorem ThreeSum.LightTernaryPairedPotential.program_digit (m : ℕ) : (program m)[3]?=some (LightRadixDigit.body 4) := by sorry

attribute [defeq] ThreeSum.LightTernaryPairedPotential.program_digit
