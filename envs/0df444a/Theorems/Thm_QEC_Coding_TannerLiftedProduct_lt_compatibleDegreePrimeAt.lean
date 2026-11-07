-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lt_compatibleDegreePrimeAt
-- name    : QEC.Coding.TannerLiftedProduct.lt_compatibleDegreePrimeAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:27:13.710779+00:00
-- url     : https://prove2.me/theorems/50c34c14-3f05-4738-b4d9-3f00d9c9e873
-- title:
--   Tanner Lifted Product: lt compatible Degree Prime At
-- statement:
--   The Tanner Lifted Product construction uses the lt compatible Degree Prime At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CompatiblePrimeDegree.lean#L141-L144
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CompatiblePrimeDegree.lean#L141-L144

import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_CompatiblePrimeDegree
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct

theorem QEC.Coding.TannerLiftedProduct.lt_compatibleDegreePrimeAt
    (A B : Nat) (hA : 0 < A) (hOdd : Odd A) :
    B < (compatibleDegreePrimeAt A B hA hOdd).p := by sorry
