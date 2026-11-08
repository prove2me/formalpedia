-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_re_eval_lpsHeckePolynomial_complex_ofReal
-- name    : QEC.Coding.TannerLiftedProduct.re_eval_lpsHeckePolynomial_complex_ofReal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:52:54.930584+00:00
-- url     : https://prove2.me/theorems/f721a365-bb79-4023-b940-d8287540aa20
-- title:
--   Tanner Lifted Product: re eval lps Hecke Polynomial complex of Real
-- statement:
--   Real evaluation of an LPS Hecke polynomial is unchanged after extension
--   of scalars to `ℂ`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRamanujanTraceBridge.lean#L180-L192
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRamanujanTraceBridge.lean#L180-L192

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSExactTraceFormula
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSpectralTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRamanujanTraceBridge
set_option autoImplicit false
open Polynomial
open scoped MatrixGroups
open Filter Asymptotics
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.re_eval_lpsHeckePolynomial_complex_ofReal
    (x : ℝ) (n : ℕ) :
    Complex.re ((lpsHeckePolynomial ℂ (p : ℂ) n).eval (x : ℂ)) =
      (lpsHeckePolynomial ℝ (p : ℝ) n).eval x := by sorry
