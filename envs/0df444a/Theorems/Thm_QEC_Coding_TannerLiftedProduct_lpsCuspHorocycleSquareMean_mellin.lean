-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHorocycleSquareMean_mellin
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspHorocycleSquareMean_mellin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:29:37.726628+00:00
-- url     : https://prove2.me/theorems/d1638663-fe25-4db9-b48e-8f94e4d9175f
-- title:
--   Tanner Lifted Product: lps Cusp Horocycle Square Mean mellin
-- statement:
--   The actual square mean has its normalized Mellin identity with the true convergent coefficient-square L-series.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspSquareLSeries.lean#L119-L158
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspSquareLSeries.lean#L119-L158

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspSquareLSeries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsCuspHorocycleSquareMean_mellin (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (s : ℂ) (hs : 2<s.re) :
    mellin (fun y : ℝ => (lpsCuspHorocycleSquareMean N f y:ℂ)) s=
      (Complex.Gamma s/((4*Real.pi:ℝ):ℂ)^s)*
        LSeries (fun n : ℕ => (lpsWeightTwoCusp_squareCoeff N f n:ℂ)) s := by sorry
