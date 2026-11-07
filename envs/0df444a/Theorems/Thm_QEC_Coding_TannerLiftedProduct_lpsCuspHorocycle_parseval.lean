-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHorocycle_parseval
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspHorocycle_parseval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:06:03.129647+00:00
-- url     : https://prove2.me/theorems/d8f6ef9d-0315-4dd2-b6da-35c84816390a
-- title:
--   Tanner Lifted Product: lps Cusp Horocycle parseval
-- statement:
--   Actual Parseval identifies the exponentially weighted q-coefficient squares with the true interval integral.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspHorocycle.lean#L292-L299
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspHorocycle.lean#L292-L299

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.NumberTheory.ModularForms.Bounds
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsCuspHorocycle_parseval (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (y : ℝ) (hy : 0<y) :
    HasSum (fun n : ℕ => ‖PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)‖^2*
      (Real.exp (-2*Real.pi*y))^(2*n))
      (∫ x in (0:ℝ)..1, ‖f (lpsHorocyclePoint y hy x)‖^2) := by sorry
