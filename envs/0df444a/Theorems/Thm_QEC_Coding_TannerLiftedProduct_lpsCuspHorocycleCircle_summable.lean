-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHorocycleCircle_summable
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspHorocycleCircle_summable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:05:34.638716+00:00
-- url     : https://prove2.me/theorems/abb451b5-46ad-46de-b61d-b9976aa6ab93
-- title:
--   Tanner Lifted Product: lps Cusp Horocycle Circle summable
-- statement:
--   The genuine horizontal Fourier series is summable at every circle point.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspHorocycle.lean#L135-L140
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspHorocycle.lean#L135-L140

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.NumberTheory.ModularForms.Bounds
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsCuspHorocycleCircle_summable (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (y : ℝ) (hy : 0<y) (x : AddCircle (1:ℝ)) :
    Summable (fun n : ℕ => lpsCuspHorocycleTerm N f y n x) := by sorry
