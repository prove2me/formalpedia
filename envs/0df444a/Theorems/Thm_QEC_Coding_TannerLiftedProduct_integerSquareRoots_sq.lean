-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_integerSquareRoots_sq
-- name    : QEC.Coding.TannerLiftedProduct.integerSquareRoots_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:35:38.155508+00:00
-- url     : https://prove2.me/theorems/f6b59957-f20b-40d8-8a35-790741fec909
-- title:
--   Tanner Lifted Product: integer Square Roots sq
-- statement:
--   A positive integral square has exactly its positive and negative roots.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/FourSquareTheta.lean#L45-L51
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/FourSquareTheta.lean#L45-L51

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionCount
import Mathlib.RingTheory.PowerSeries.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset

theorem QEC.Coding.TannerLiftedProduct.integerSquareRoots_sq (m : ℕ) :
    integerSquareRoots (m ^ 2) = {(m : ℤ), -(m : ℤ)} := by sorry
