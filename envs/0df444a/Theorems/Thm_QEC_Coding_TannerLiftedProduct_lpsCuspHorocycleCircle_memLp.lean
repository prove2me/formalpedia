-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHorocycleCircle_memLp
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspHorocycleCircle_memLp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:18:06.250972+00:00
-- url     : https://prove2.me/theorems/8d6674f2-4cf4-430c-b5c8-ae9e7eb14bd4
-- title:
--   Tanner Lifted Product: lps Cusp Horocycle Circle mem Lp
-- statement:
--   The actual continuous horizontal circle function is square integrable.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspHorocycle.lean#L217-L222
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspHorocycle.lean#L217-L222

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.NumberTheory.ModularForms.Bounds
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsCuspHorocycleCircle_memLp (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (y : ℝ) (hy : 0<y) :
    MemLp (lpsCuspHorocycleCircle N f y) 2 (@AddCircle.haarAddCircle 1 ⟨by norm_num⟩) := by sorry
