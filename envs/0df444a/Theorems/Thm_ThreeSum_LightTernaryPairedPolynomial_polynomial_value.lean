-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryPairedPolynomial_polynomial_value
-- name    : ThreeSum.LightTernaryPairedPolynomial.polynomial_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:29:29.576779+00:00
-- url     : https://prove2.me/theorems/849fa6c2-8474-4afb-b66f-38397babd5ff
-- title:
--   Light Ternary Paired Polynomial: polynomial value
-- statement:
--   The Light Ternary Paired Polynomial construction uses the polynomial value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPairedPolynomial.lean#L109-L120
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPairedPolynomial.lean#L109-L120

import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Definitions.Def_Submission_ThreeSum_TernaryPairedTensor
import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPolynomial
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryPairedPolynomial
open Light LightFixedArithmetic LightMomentDeterminant TernaryPairedTensor
open scoped BigOperators

theorem ThreeSum.LightTernaryPairedPolynomial.polynomial_value (m : ℕ) (T : Quad m → ℤ) (σ : State)
    (hT : ∀ q, (atomExpr m q).val σ=T q) :
    ((polynomial m).compile (atoms m)).val σ=value T := by sorry
