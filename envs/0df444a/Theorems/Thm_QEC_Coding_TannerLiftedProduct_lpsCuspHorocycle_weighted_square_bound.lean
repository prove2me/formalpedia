-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHorocycle_weighted_square_bound
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspHorocycle_weighted_square_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:18:19.971035+00:00
-- url     : https://prove2.me/theorems/5020da38-ef7b-486b-826d-0ade8474f0b9
-- title:
--   Tanner Lifted Product: lps Cusp Horocycle weighted square bound
-- statement:
--   The genuine cusp bound controls the sum of actual exponentially weighted coefficient squares.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspHorocycle.lean#L316-L324
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspHorocycle.lean#L316-L324

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.NumberTheory.ModularForms.Bounds
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsCuspHorocycle_weighted_square_bound (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    ∃ C : ℝ, 0≤C ∧ ∀ (y : ℝ) (_hy : 0<y),
      (∑' n : ℕ, ‖PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)‖^2*
        (Real.exp (-2*Real.pi*y))^(2*n))≤(C/y)^2 := by sorry
