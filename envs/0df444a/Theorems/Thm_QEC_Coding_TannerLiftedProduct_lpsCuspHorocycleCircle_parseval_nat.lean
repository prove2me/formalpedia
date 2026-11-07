-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHorocycleCircle_parseval_nat
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspHorocycleCircle_parseval_nat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:15:38.247574+00:00
-- url     : https://prove2.me/theorems/97dc6e8a-ddd6-400e-b8a4-52c9c6686b57
-- title:
--   Tanner Lifted Product: lps Cusp Horocycle Circle parseval nat
-- statement:
--   Vanishing negative frequencies gives the actual natural-indexed coefficient-square Parseval sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspHorocycle.lean#L240-L262
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspHorocycle.lean#L240-L262

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.NumberTheory.ModularForms.Bounds
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsCuspHorocycleCircle_parseval_nat (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (y : ℝ) (hy : 0<y) :
    HasSum (fun n : ℕ => ‖PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)‖^2*
      (Real.exp (-2*Real.pi*y))^(2*n))
      (∫ x : AddCircle (1:ℝ), ‖lpsCuspHorocycleCircle N f y x‖^2 ∂AddCircle.haarAddCircle) := by sorry
