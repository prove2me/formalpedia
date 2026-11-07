-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPSLIndexInv_mul
-- name    : QEC.Coding.TannerLiftedProduct.lpsPSLIndexInv_mul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T01:55:12.481848+00:00
-- url     : https://prove2.me/theorems/a114e6c8-615c-4c1c-ae44-c7ba19c31263
-- title:
--   Tanner Lifted Product: lps PSLIndex Inv mul
-- statement:
--   The computed inverse index multiplies back to the actual identity index.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSVertexEnumeration.lean#L156-L161
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSVertexEnumeration.lean#L156-L161

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveNormalization
import Mathlib.Data.List.FinRange
import Mathlib.Data.Quot
import Mathlib.Data.List.NodupEquivFin
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSVertexEnumeration
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_747ca7d85c_18

theorem QEC.Coding.TannerLiftedProduct.lpsPSLIndexInv_mul (q : ℕ) [Fact q.Prime]
    (i : Fin (lpsPSLList q).length) :
    lpsPSLIndexMul q (lpsPSLIndexInv q i) i = lpsPSLIndexOne q := by sorry
