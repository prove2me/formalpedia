-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryPairedPotential_program_divide
-- name    : ThreeSum.LightTernaryPairedPotential.program_divide
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:49:17.43627+00:00
-- url     : https://prove2.me/theorems/738027d2-17be-4502-9d8f-97a150dd6627
-- title:
--   Light Ternary Paired Potential: program divide
-- statement:
--   The Light Ternary Paired Potential construction uses the program divide property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPairedPotential.lean#L260-L260
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPairedPotential.lean#L260-L260

import Definitions.Def_Submission_ThreeSum_TernaryPairedColumnEnumeration
import Definitions.Def_Submission_ThreeSum_LightWeightRow
import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPotential
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryPairedPotential
open Light LightTernaryPairedPolynomial TernaryPairedColumnEnumeration TernaryPairedTensor
open scoped BigOperators

theorem ThreeSum.LightTernaryPairedPotential.program_divide (m : ℕ) : (program m)[4]?=some LightSmallDivide.body := by sorry

attribute [defeq] ThreeSum.LightTernaryPairedPotential.program_divide
