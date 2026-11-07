-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwoCusp_squareCoeff_sum_isBigO
-- name    : QEC.Coding.TannerLiftedProduct.lpsWeightTwoCusp_squareCoeff_sum_isBigO
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:42:33.505932+00:00
-- url     : https://prove2.me/theorems/a4538712-cee9-4556-a75c-ad8b9dec6da4
-- title:
--   Tanner Lifted Product: lps Weight Two Cusp square Coeff sum is Big O
-- statement:
--   The proved quadratic square-average bound gives the actual inclusive partial-sum asymptotic bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspSquareLSeries.lean#L37-L58
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspSquareLSeries.lean#L37-L58

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspSquareLSeries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsWeightTwoCusp_squareCoeff_sum_isBigO (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    (fun X : ℕ => ∑ n ∈ Finset.Icc 1 X, lpsWeightTwoCusp_squareCoeff N f n)
      =O[atTop] (fun X : ℕ => (X:ℝ)^(2:ℝ)) := by sorry
