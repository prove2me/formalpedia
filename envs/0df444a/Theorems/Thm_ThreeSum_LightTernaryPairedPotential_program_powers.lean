-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryPairedPotential_program_powers
-- name    : ThreeSum.LightTernaryPairedPotential.program_powers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:49:12.452507+00:00
-- url     : https://prove2.me/theorems/09e60674-79b2-4bb5-8af8-20569302353e
-- title:
--   Light Ternary Paired Potential: program powers
-- statement:
--   The Light Ternary Paired Potential construction uses the program powers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPairedPotential.lean#L257-L257
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPairedPotential.lean#L257-L257

import Definitions.Def_Submission_ThreeSum_TernaryPairedColumnEnumeration
import Definitions.Def_Submission_ThreeSum_LightWeightRow
import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPotential
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryPairedPotential
open Light LightTernaryPairedPolynomial TernaryPairedColumnEnumeration TernaryPairedTensor
open scoped BigOperators

theorem ThreeSum.LightTernaryPairedPotential.program_powers (m : ℕ) : (program m)[1]?=some powTableBody := by sorry

attribute [defeq] ThreeSum.LightTernaryPairedPotential.program_powers
