-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalSigmaZSeries_constant
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalSigmaZSeries_constant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:17:52.20996+00:00
-- url     : https://prove2.me/theorems/0ffccdc6-de44-4f9c-a6b4-2ada7b951c2c
-- title:
--   Tanner Lifted Product: lps Original Sigma ZSeries constant
-- statement:
--   The actual mapped integer divisor-sum series has zero constant coefficient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerQExpansion.lean#L49-L53
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerQExpansion.lean#L49-L53

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalQExpansionArithmetic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerQExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalSigmaZSeries_constant (k : ℕ) :
    PowerSeries.constantCoeff
      (PowerSeries.map (algebraMap ℤ ℚ) (lpsOriginalSigmaZSeries k))=0 := by sorry
