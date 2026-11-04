-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryPairedPolynomial_tensorIndex_lt
-- name    : ThreeSum.LightTernaryPairedPolynomial.tensorIndex_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:43:26.063063+00:00
-- url     : https://prove2.me/theorems/a07f6d33-e5a6-494d-a9b9-7b424fb5da95
-- title:
--   Light Ternary Paired Polynomial: tensor Index lt
-- statement:
--   The Light Ternary Paired Polynomial construction uses the tensor Index lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPairedPolynomial.lean#L46-L51
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPairedPolynomial.lean#L46-L51

import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Definitions.Def_Submission_ThreeSum_TernaryPairedTensor
import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPolynomial
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryPairedPolynomial
open Light LightFixedArithmetic LightMomentDeterminant TernaryPairedTensor
open scoped BigOperators

theorem ThreeSum.LightTernaryPairedPolynomial.tensorIndex_lt {Λ a b c d : ℕ} (ha : a<Λ) (hb : b<Λ) (hc : c<Λ) (hd : d<Λ) :
    tensorIndex Λ a b c d < Λ^4 := by sorry
