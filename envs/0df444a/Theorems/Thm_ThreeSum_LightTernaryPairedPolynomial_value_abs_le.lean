-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryPairedPolynomial_value_abs_le
-- name    : ThreeSum.LightTernaryPairedPolynomial.value_abs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:29:30.838321+00:00
-- url     : https://prove2.me/theorems/87bfae6a-0804-4934-898e-c1c148069273
-- title:
--   Light Ternary Paired Polynomial: value abs le
-- statement:
--   The Light Ternary Paired Polynomial construction uses the value abs le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPairedPolynomial.lean#L83-L107
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPairedPolynomial.lean#L83-L107

import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Definitions.Def_Submission_ThreeSum_TernaryPairedTensor
import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPolynomial
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryPairedPolynomial
open Light LightFixedArithmetic LightMomentDeterminant TernaryPairedTensor
open scoped BigOperators

theorem ThreeSum.LightTernaryPairedPolynomial.value_abs_le {m : ℕ} (T : Quad m → ℤ) (U : ℤ) (hU : 0≤U)
    (hT : ∀ q, |T q|≤U) : |value T|≤(polynomial m).bound U := by sorry
