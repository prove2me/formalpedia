-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryPairedPotential_program_row
-- name    : ThreeSum.LightTernaryPairedPotential.program_row
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:49:23.993179+00:00
-- url     : https://prove2.me/theorems/3b181db7-00a3-4ec8-9f65-0334c8e22029
-- title:
--   Light Ternary Paired Potential: program row
-- statement:
--   The Light Ternary Paired Potential construction uses the program row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPairedPotential.lean#L258-L258
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPairedPotential.lean#L258-L258

import Definitions.Def_Submission_ThreeSum_TernaryPairedColumnEnumeration
import Definitions.Def_Submission_ThreeSum_LightWeightRow
import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPotential
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryPairedPotential
open Light LightTernaryPairedPolynomial TernaryPairedColumnEnumeration TernaryPairedTensor
open scoped BigOperators

theorem ThreeSum.LightTernaryPairedPotential.program_row (m : ℕ) : (program m)[2]?=some (LightWeightRow.body 3) := by sorry

attribute [defeq] ThreeSum.LightTernaryPairedPotential.program_row
