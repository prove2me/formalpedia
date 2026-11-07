-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHorocycleCircle_coe
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspHorocycleCircle_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:15:46.200022+00:00
-- url     : https://prove2.me/theorems/be540c03-ed43-44ab-9464-8669f86ce7c0
-- title:
--   Tanner Lifted Product: lps Cusp Horocycle Circle coe
-- statement:
--   The actual circle expansion agrees with the original cusp form on the whole horizontal line.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspHorocycle.lean#L119-L132
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspHorocycle.lean#L119-L132

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.NumberTheory.ModularForms.Bounds
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsCuspHorocycleCircle_coe (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (y : ℝ) (hy : 0<y) (x : ℝ) :
    lpsCuspHorocycleCircle N f y (x:AddCircle (1:ℝ))=f (lpsHorocyclePoint y hy x) := by sorry
