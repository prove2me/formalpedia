-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwoCusp_squareLSeries_eq_abel_integral
-- name    : QEC.Coding.TannerLiftedProduct.lpsWeightTwoCusp_squareLSeries_eq_abel_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:29:18.427682+00:00
-- url     : https://prove2.me/theorems/adb0d560-b672-43a0-a5ba-0c58a5278d20
-- title:
--   Tanner Lifted Product: lps Weight Two Cusp square LSeries eq abel integral
-- statement:
--   The actual convergent square L-series has its true Abel integral representation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspSquareLSeries.lean#L70-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspSquareLSeries.lean#L70-L79

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspSquareLSeries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsWeightTwoCusp_squareLSeries_eq_abel_integral (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (s : ℂ) (hs : 2<s.re) :
    LSeries (fun n : ℕ => (lpsWeightTwoCusp_squareCoeff N f n:ℂ)) s=
      s*(∫ t in Set.Ioi (1:ℝ),
        (∑ n ∈ Finset.Icc 1 ⌊t⌋₊, (lpsWeightTwoCusp_squareCoeff N f n:ℂ))*
          (t:ℂ)^(-(s+1))) := by sorry
