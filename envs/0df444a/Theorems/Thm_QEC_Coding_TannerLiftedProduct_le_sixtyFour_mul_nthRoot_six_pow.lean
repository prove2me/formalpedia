-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_le_sixtyFour_mul_nthRoot_six_pow
-- name    : QEC.Coding.TannerLiftedProduct.le_sixtyFour_mul_nthRoot_six_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:27:01.491217+00:00
-- url     : https://prove2.me/theorems/5b67f54f-7375-42dc-ad4a-5060919993f5
-- title:
--   Tanner Lifted Product: le sixty Four mul nth Root six pow
-- statement:
--   Every positive block quotient is within a factor `64 = 2^6` of the
--   sixth power of its floored sixth root.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CompatiblePrimeDegree.lean#L45-L60
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CompatiblePrimeDegree.lean#L45-L60

import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_CompatiblePrimeDegree
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct

theorem QEC.Coding.TannerLiftedProduct.le_sixtyFour_mul_nthRoot_six_pow
    (n : Nat) (hn : 0 < n) :
    n ≤ 64 * (Nat.nthRoot 6 n) ^ 6 := by sorry
