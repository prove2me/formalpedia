-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryPairedPotential_program_polynomial
-- name    : ThreeSum.LightTernaryPairedPotential.program_polynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:49:31.020834+00:00
-- url     : https://prove2.me/theorems/89ce494e-e1a6-4000-8705-74494f38cb99
-- title:
--   Light Ternary Paired Potential: program polynomial
-- statement:
--   The Light Ternary Paired Potential construction uses the program polynomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPairedPotential.lean#L261-L261
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPairedPotential.lean#L261-L261

import Definitions.Def_Submission_ThreeSum_TernaryPairedColumnEnumeration
import Definitions.Def_Submission_ThreeSum_LightWeightRow
import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPotential
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryPairedPotential
open Light LightTernaryPairedPolynomial TernaryPairedColumnEnumeration TernaryPairedTensor
open scoped BigOperators

theorem ThreeSum.LightTernaryPairedPotential.program_polynomial (m : ℕ) : (program m)[5]?=some (LightTernaryPairedPolynomial.body m) := by sorry

attribute [defeq] ThreeSum.LightTernaryPairedPotential.program_polynomial
