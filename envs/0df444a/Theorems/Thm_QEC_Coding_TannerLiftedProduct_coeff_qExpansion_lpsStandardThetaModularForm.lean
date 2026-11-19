-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_qExpansion_lpsStandardThetaModularForm
-- name    : QEC.Coding.TannerLiftedProduct.coeff_qExpansion_lpsStandardThetaModularForm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:34:13.255385+00:00
-- url     : https://prove2.me/theorems/eeb7e63d-0b3e-49f2-9035-1101db021b7c
-- title:
--   Tanner Lifted Product: coeff q Expansion lps Standard Theta Modular Form
-- statement:
--   The genuine modular form has exactly the already-proved trace theta coefficients.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaModularForm.lean#L108-L111
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaModularForm.lean#L108-L111

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaGaussFourthReduction
import Mathlib.NumberTheory.ModularForms.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaModularForm
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.coeff_qExpansion_lpsStandardThetaModularForm (q : ℕ) (hq : 0<q) (n : ℕ) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (lpsStandardThetaModularForm q hq)) =
      ((PowerSeries.coeff n (lpsTraceThetaSeries q) : ℕ) : ℂ) := by sorry
