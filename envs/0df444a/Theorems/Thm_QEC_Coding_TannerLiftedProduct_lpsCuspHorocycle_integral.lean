-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHorocycle_integral
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspHorocycle_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:18:14.551455+00:00
-- url     : https://prove2.me/theorems/19eba2c0-5044-4107-bbb7-8eda6bfbf93f
-- title:
--   Tanner Lifted Product: lps Cusp Horocycle integral
-- statement:
--   The normalized Haar square integral is exactly the original horizontal interval integral.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspHorocycle.lean#L281-L289
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspHorocycle.lean#L281-L289

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.NumberTheory.ModularForms.Bounds
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsCuspHorocycle_integral (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (y : ℝ) (hy : 0<y) :
    (∫ x : AddCircle (1:ℝ), ‖lpsCuspHorocycleCircle N f y x‖^2 ∂AddCircle.haarAddCircle)=
      ∫ x in (0:ℝ)..1, ‖f (lpsHorocyclePoint y hy x)‖^2 := by sorry
