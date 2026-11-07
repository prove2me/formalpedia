-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHorocycle_integral_bound_of_norm_bound
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspHorocycle_integral_bound_of_norm_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:18:16.917586+00:00
-- url     : https://prove2.me/theorems/e61a2cd8-2bee-4ead-a195-81ac011b0f22
-- title:
--   Tanner Lifted Product: lps Cusp Horocycle integral bound of norm bound
-- statement:
--   A pointwise bound on the actual horizontal function bounds its true square integral.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspHorocycle.lean#L302-L313
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspHorocycle.lean#L302-L313

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.NumberTheory.ModularForms.Bounds
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsCuspHorocycle_integral_bound_of_norm_bound (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (C y : ℝ) (hy : 0<y)
    (hb : ∀ x : AddCircle (1:ℝ), ‖lpsCuspHorocycleCircle N f y x‖≤C/y) :
    (∫ x : AddCircle (1:ℝ), ‖lpsCuspHorocycleCircle N f y x‖^2 ∂AddCircle.haarAddCircle)≤
      (C/y)^2 := by sorry
