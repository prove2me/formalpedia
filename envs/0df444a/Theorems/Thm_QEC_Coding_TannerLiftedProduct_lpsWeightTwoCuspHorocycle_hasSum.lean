-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwoCuspHorocycle_hasSum
-- name    : QEC.Coding.TannerLiftedProduct.lpsWeightTwoCuspHorocycle_hasSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:15:36.722374+00:00
-- url     : https://prove2.me/theorems/30774cb0-dba3-459c-b3bb-f01073bd1f3a
-- title:
--   Tanner Lifted Product: lps Weight Two Cusp Horocycle has Sum
-- statement:
--   The actual weight-two cusp form has its genuine q-expansion sum at every horizontal point.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspHorocycle.lean#L42-L52
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspHorocycle.lean#L42-L52

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.NumberTheory.ModularForms.Bounds
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsWeightTwoCuspHorocycle_hasSum (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (y : ℝ) (hy : 0<y) (x : ℝ) :
    HasSum (fun n : ℕ => PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)*
      (Function.Periodic.qParam 1 (lpsHorocyclePoint y hy x:ℂ))^n)
      (f (lpsHorocyclePoint y hy x)) := by sorry
