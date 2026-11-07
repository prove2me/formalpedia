-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_abs_eigenvalues_le_of_trace_evenPow_isBigO
-- name    : QEC.Coding.TannerLiftedProduct.abs_eigenvalues_le_of_trace_evenPow_isBigO
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:12:50.105196+00:00
-- url     : https://prove2.me/theorems/53760591-42ca-45d0-8362-9f0d04a85e96
-- title:
--   Tanner Lifted Product: abs eigenvalues le of trace even Pow is Big O
-- statement:
--   The exact finite-dimensional LPS endgame: if every exponential rate
--   above `r` bounds the even traces, then every eigenvalue lies in `[-r,r]`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSpectralTrace.lean#L59-L72
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSpectralTrace.lean#L59-L72

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

theorem QEC.Coding.TannerLiftedProduct.abs_eigenvalues_le_of_trace_evenPow_isBigO
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric)
    {r : ℝ} (hr : 0 ≤ r)
    (hTrace : ∀ s : ℝ, r < s →
      (fun n : ℕ =>
        Complex.re (LinearMap.trace ℂ E (T ^ (2 * n)))) =O[atTop]
          fun n : ℕ => s ^ (2 * n)) :
    ∀ i : Fin (Module.finrank ℂ E),
      |hT.eigenvalues rfl i| ≤ r := by sorry
