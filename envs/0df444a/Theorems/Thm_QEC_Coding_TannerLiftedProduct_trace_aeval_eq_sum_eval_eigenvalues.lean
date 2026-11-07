-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_trace_aeval_eq_sum_eval_eigenvalues
-- name    : QEC.Coding.TannerLiftedProduct.trace_aeval_eq_sum_eval_eigenvalues
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:22:39.85606+00:00
-- url     : https://prove2.me/theorems/d8be19a9-79d5-40dd-b475-667141dee012
-- title:
--   Tanner Lifted Product: trace aeval eq sum eval eigenvalues
-- statement:
--   Polynomial functional calculus followed by trace is the sum of the
--   polynomial over the real self-adjoint eigenvalues.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSpectralTrace.lean#L25-L38
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSpectralTrace.lean#L25-L38

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

theorem QEC.Coding.TannerLiftedProduct.trace_aeval_eq_sum_eval_eigenvalues
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (P : ℂ[X]) :
    LinearMap.trace ℂ E (aeval T P) =
      ∑ i : Fin (Module.finrank ℂ E),
        P.eval (hT.eigenvalues rfl i : ℂ) := by sorry
