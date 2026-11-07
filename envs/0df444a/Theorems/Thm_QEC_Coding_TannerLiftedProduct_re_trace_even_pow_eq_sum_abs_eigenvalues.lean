-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_re_trace_even_pow_eq_sum_abs_eigenvalues
-- name    : QEC.Coding.TannerLiftedProduct.re_trace_even_pow_eq_sum_abs_eigenvalues
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:22:38.493397+00:00
-- url     : https://prove2.me/theorems/817cb6fd-9fe4-491b-bbd9-ebd8659b54cf
-- title:
--   Tanner Lifted Product: re trace even pow eq sum abs eigenvalues
-- statement:
--   The real trace of an even power is the nonnegative even spectral
--   moment.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSpectralTrace.lean#L42-L55
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSpectralTrace.lean#L42-L55

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSMomentBound
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSpectralTrace
set_option autoImplicit false
open Filter Asymptotics
open Polynomial
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

theorem QEC.Coding.TannerLiftedProduct.re_trace_even_pow_eq_sum_abs_eigenvalues
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (n : ℕ) :
    Complex.re (LinearMap.trace ℂ E (T ^ (2 * n))) =
      ∑ i : Fin (Module.finrank ℂ E),
        |hT.eigenvalues rfl i| ^ (2 * n) := by sorry
