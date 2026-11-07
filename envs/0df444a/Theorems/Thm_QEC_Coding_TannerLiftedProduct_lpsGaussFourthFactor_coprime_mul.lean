-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGaussFourthFactor_coprime_mul
-- name    : QEC.Coding.TannerLiftedProduct.lpsGaussFourthFactor_coprime_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:48:58.484187+00:00
-- url     : https://prove2.me/theorems/722b08d8-6ede-45ed-a03e-371c88ef7d8e
-- title:
--   Tanner Lifted Product: lps Gauss Fourth Factor coprime mul
-- statement:
--   The residue factor multiplies at coprime moduli because both cannot be even.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L431-L450
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L431-L450

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex

theorem QEC.Coding.TannerLiftedProduct.lpsGaussFourthFactor_coprime_mul (m n : ℕ) (h : m.Coprime n) :
    lpsGaussFourthFactor (m*n)=lpsGaussFourthFactor m*lpsGaussFourthFactor n := by sorry
