-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHorocycleCircle_continuous
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspHorocycleCircle_continuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:15:52.115729+00:00
-- url     : https://prove2.me/theorems/cabb80aa-cbfb-4ce8-a3dc-8eea3faee463
-- title:
--   Tanner Lifted Product: lps Cusp Horocycle Circle continuous
-- statement:
--   The norm-summable actual coefficient expansion defines a continuous circle function.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspHorocycle.lean#L110-L116
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspHorocycle.lean#L110-L116

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.NumberTheory.ModularForms.Bounds
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsCuspHorocycleCircle_continuous (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (y : ℝ) (hy : 0<y) : Continuous (lpsCuspHorocycleCircle N f y) := by sorry
