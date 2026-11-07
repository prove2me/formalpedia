-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJN_mem_Q_of_finiteRationalSeriesEquation
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJN_mem_Q_of_finiteRationalSeriesEquation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:20:45.267198+00:00
-- url     : https://prove2.me/theorems/3a190946-2a23-4116-99a7-28ecead3b8e3
-- title:
--   Tanner Lifted Product: lps Original JN mem Q of finite Rational Series Equation
-- statement:
--   Actual rational finite-series equation recovers the original jN in Q(j,jM).
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalLevelInclusion.lean#L441-L516
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalLevelInclusion.lean#L441-L516

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJN_mem_Q_of_finiteRationalSeriesEquation
    {ι : Type*} [Fintype ι] (N M : ℕ) (hN : 0 < N) (hM : 0 < M)
    (B : ℕ) (u v : ι → ℕ) (a b : ι → ℚ)
    (hB : ∀ i, u i + M * v i ≤ B)
    (h :
      PowerSeries.X ^ N * (∑ i, PowerSeries.C (a i) *
        lpsOriginalClearedFormalMonomial M (Nat.ne_of_gt hM) B (u i) (v i)) =
      PowerSeries.expand N (Nat.ne_of_gt hN) lpsOriginalJQSeries *
        (∑ i, PowerSeries.C (b i) *
          lpsOriginalClearedFormalMonomial M (Nat.ne_of_gt hM) B (u i) (v i)))
    (hb : (∑ i, PowerSeries.C (b i) *
      lpsOriginalClearedFormalMonomial M (Nat.ne_of_gt hM) B (u i) (v i)) ≠ 0) :
    lpsOriginalJNInFractionField N hN ∈ lpsOriginalGeneratedFunctionFieldQ M hM := by sorry
