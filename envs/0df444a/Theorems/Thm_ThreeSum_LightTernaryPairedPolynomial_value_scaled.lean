-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryPairedPolynomial_value_scaled
-- name    : ThreeSum.LightTernaryPairedPolynomial.value_scaled
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:29:24.603213+00:00
-- url     : https://prove2.me/theorems/4f67e73d-9e21-464f-8ed6-a5ee2718a994
-- title:
--   Light Ternary Paired Polynomial: value scaled
-- statement:
--   The Light Ternary Paired Polynomial construction uses the value scaled property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPairedPolynomial.lean#L71-L81
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPairedPolynomial.lean#L71-L81

import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Definitions.Def_Submission_ThreeSum_TernaryPairedTensor
import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPolynomial
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryPairedPolynomial
open Light LightFixedArithmetic LightMomentDeterminant TernaryPairedTensor
open scoped BigOperators

theorem ThreeSum.LightTernaryPairedPolynomial.value_scaled {m : ℕ} (T : Quad m → ℤ) (s : ℤ) :
    value (fun q => s*T q)=s^m*value T := by sorry
