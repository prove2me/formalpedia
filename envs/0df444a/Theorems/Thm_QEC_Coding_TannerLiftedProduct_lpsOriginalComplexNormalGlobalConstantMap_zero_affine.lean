-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalComplexNormalGlobalConstantMap_zero_affine
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalComplexNormalGlobalConstantMap_zero_affine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T06:58:48.556319+00:00
-- url     : https://prove2.me/theorems/411d4678-632b-41e1-8b70-924db7f13ac4
-- title:
--   Tanner Lifted Product: lps Original Complex Normal Global Constant Map zero affine
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Complex Normal Global Constant Map zero affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDifferentialSheaf.lean#L125-L133
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDifferentialSheaf.lean#L125-L133

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineDifferentials
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalComplexNormalCharts
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialSheaf
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open CategoryTheory _root_.AlgebraicGeometry QEC.Coding.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N)
local notation "X" => lpsOriginalComplexNormalGluedScheme N hpos
local notation "Z" => lpsOriginalComplexNormalZeroChart N hpos
local notation "I" => lpsOriginalComplexNormalInfinityChart N hpos
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalZeroChartDifferentialAlgebra
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalInfinityChartDifferentialAlgebra
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalZeroChartDifferentialSMul
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalZeroChartDifferentialModule
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalZeroChartDifferentialSMulComm
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalZeroChartOmegaSMul
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalZeroChartOmegaModule
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalInfinityChartDifferentialSMul
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalInfinityChartDifferentialModule
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalInfinityChartDifferentialSMulComm
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalInfinityChartOmegaSMul
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalInfinityChartOmegaModule

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalComplexNormalGlobalConstantMap_zero_affine :
    lpsOriginalComplexNormalGlobalConstantMap N hpos ≫
      (lpsOriginalComplexNormalGluedChartMap N hpos false).appTop =
    affineDifferentialGlobalConstantMap ℂ (CommRingCat.of Z) := by sorry
