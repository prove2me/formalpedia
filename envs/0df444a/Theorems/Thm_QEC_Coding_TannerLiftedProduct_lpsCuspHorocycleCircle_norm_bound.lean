-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHorocycleCircle_norm_bound
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspHorocycleCircle_norm_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:18:16.686251+00:00
-- url     : https://prove2.me/theorems/181e1245-bb6d-4ccc-8f00-fd7f0c54d479
-- title:
--   Tanner Lifted Product: lps Cusp Horocycle Circle norm bound
-- statement:
--   The genuine weight-two cusp bound gives one constant for every positive-height circle.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspHorocycle.lean#L265-L278
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspHorocycle.lean#L265-L278

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.NumberTheory.ModularForms.Bounds
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsCuspHorocycleCircle_norm_bound (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    ∃ C : ℝ, 0≤C ∧ ∀ (y : ℝ) (_hy : 0<y) (x : AddCircle (1:ℝ)),
      ‖lpsCuspHorocycleCircle N f y x‖≤C/y := by sorry
