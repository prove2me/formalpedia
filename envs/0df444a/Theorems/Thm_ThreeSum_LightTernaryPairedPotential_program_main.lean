-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryPairedPotential_program_main
-- name    : ThreeSum.LightTernaryPairedPotential.program_main
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:49:01.841638+00:00
-- url     : https://prove2.me/theorems/4ceccea8-7a60-419c-9384-f707e7cad551
-- title:
--   Light Ternary Paired Potential: program main
-- statement:
--   The Light Ternary Paired Potential construction uses the program main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPairedPotential.lean#L256-L256
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPairedPotential.lean#L256-L256

import Definitions.Def_Submission_ThreeSum_TernaryPairedColumnEnumeration
import Definitions.Def_Submission_ThreeSum_LightWeightRow
import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPotential
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryPairedPotential
open Light LightTernaryPairedPolynomial TernaryPairedColumnEnumeration TernaryPairedTensor
open scoped BigOperators

theorem ThreeSum.LightTernaryPairedPotential.program_main (m : ℕ) : (program m)[0]?=some (body m 1 2 5) := by sorry

attribute [defeq] ThreeSum.LightTernaryPairedPotential.program_main
