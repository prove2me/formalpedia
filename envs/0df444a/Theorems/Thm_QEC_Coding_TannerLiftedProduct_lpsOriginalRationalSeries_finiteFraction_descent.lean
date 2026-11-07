-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalSeries_finiteFraction_descent
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRationalSeries_finiteFraction_descent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:20:52.124744+00:00
-- url     : https://prove2.me/theorems/dc0270b8-c53b-42b2-bfd6-3b93849ff04f
-- title:
--   Tanner Lifted Product: lps Original Rational Series finite Fraction descent
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Rational Series finite Fraction descent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalLevelInclusion.lean#L209-L273
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalLevelInclusion.lean#L209-L273

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullFieldLevelPullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeFunctionFieldDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalLevelInclusion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRationalSeries_finiteFraction_descent
    {ι : Type*} [Fintype ι]
    (A U : PowerSeries ℚ) (T : ι → PowerSeries ℚ) (a b : ι → ℂ)
    (h : PowerSeries.map (algebraMap ℚ ℂ) A *
          (∑ i, PowerSeries.C (a i) * PowerSeries.map (algebraMap ℚ ℂ) (T i)) =
        PowerSeries.map (algebraMap ℚ ℂ) U *
          (∑ i, PowerSeries.C (b i) * PowerSeries.map (algebraMap ℚ ℂ) (T i)))
    (hS : (∑ i, PowerSeries.C (b i) *
      PowerSeries.map (algebraMap ℚ ℂ) (T i)) ≠ 0) :
    ∃ aq bq : ι → ℚ,
      A * (∑ i, PowerSeries.C (aq i) * T i) =
        U * (∑ i, PowerSeries.C (bq i) * T i) ∧
      (∑ i, PowerSeries.C (bq i) * T i) ≠ 0 := by sorry
