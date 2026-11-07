-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwoCusp_coeff_square_sum_bound
-- name    : QEC.Coding.TannerLiftedProduct.lpsWeightTwoCusp_coeff_square_sum_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:42:12.283191+00:00
-- url     : https://prove2.me/theorems/fc8ceae4-dee5-4118-8c4f-51805f364239
-- title:
--   Tanner Lifted Product: lps Weight Two Cusp coeff square sum bound
-- statement:
--   The actual weight-two coefficients have one quadratic square-average bound for every finite initial range.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspHorocycle.lean#L335-L381
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspHorocycle.lean#L335-L381

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.NumberTheory.ModularForms.Bounds
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsWeightTwoCusp_coeff_square_sum_bound (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    ∃ C : ℝ, 0≤C ∧ ∀ X : ℕ,
      (∑ n ∈ Finset.range X, ‖PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)‖^2)≤
        C*(X:ℝ)^2 := by sorry
