-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryPairedPolynomial_atoms_encode
-- name    : ThreeSum.LightTernaryPairedPolynomial.atoms_encode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:29:38.64607+00:00
-- url     : https://prove2.me/theorems/304e7d75-4c0f-479f-a8bd-790e0225547e
-- title:
--   Light Ternary Paired Polynomial: atoms encode
-- statement:
--   The Light Ternary Paired Polynomial construction uses the atoms encode property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPairedPolynomial.lean#L61-L64
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPairedPolynomial.lean#L61-L64

import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Definitions.Def_Submission_ThreeSum_TernaryPairedTensor
import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPolynomial
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryPairedPolynomial
open Light LightFixedArithmetic LightMomentDeterminant TernaryPairedTensor
open scoped BigOperators

theorem ThreeSum.LightTernaryPairedPolynomial.atoms_encode (m : ℕ) (q : Quad m) : atoms m (encode q) = atomExpr m q := by sorry
