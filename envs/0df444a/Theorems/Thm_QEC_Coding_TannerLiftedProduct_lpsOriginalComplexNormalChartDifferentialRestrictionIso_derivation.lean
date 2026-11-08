-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalComplexNormalChartDifferentialRestrictionIso_derivation
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalComplexNormalChartDifferentialRestrictionIso_derivation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:37:52.836556+00:00
-- url     : https://prove2.me/theorems/0b6e8954-5d54-4fe9-97fc-cfae75a4bfab
-- title:
--   Tanner Lifted Product: lps Original Complex Normal Chart Differential Restriction Iso derivation
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Complex Normal Chart Differential Restriction Iso derivation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDifferentialRestriction.lean#L42-L50
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDifferentialRestriction.lean#L42-L50

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeRestriction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialSheaf
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialRestriction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open CategoryTheory _root_.AlgebraicGeometry QEC.Coding.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N)
local notation "X" => lpsOriginalComplexNormalGluedScheme N hpos
local notation "Z" => lpsOriginalComplexNormalZeroChart N hpos
local notation "I" => lpsOriginalComplexNormalInfinityChart N hpos
local notation "c" => lpsOriginalComplexNormalGlobalConstantMap N hpos
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalChartDifferentialRestrictionOpenImmersion
attribute [local instance] lpsOriginalZeroChartDifferentialAlgebra
  lpsOriginalInfinityChartDifferentialAlgebra lpsOriginalZeroChartDifferentialSMul
  lpsOriginalZeroChartDifferentialModule lpsOriginalZeroChartDifferentialSMulComm
  lpsOriginalZeroChartOmegaSMul lpsOriginalZeroChartOmegaModule
  lpsOriginalInfinityChartDifferentialSMul lpsOriginalInfinityChartDifferentialModule
  lpsOriginalInfinityChartDifferentialSMulComm lpsOriginalInfinityChartOmegaSMul
  lpsOriginalInfinityChartOmegaModule

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalComplexNormalChartDifferentialRestrictionIso_derivation (b : Bool) :
    (schemeDifferentialSheafDerivation (lpsOriginalComplexNormalSchemeChart N hpos b)
      (CommRingCat.of ℂ) (c ≫ (lpsOriginalComplexNormalGluedChartMap N hpos b).appTop)).postcomp
      ((Scheme.Modules.toPresheafOfModules (lpsOriginalComplexNormalSchemeChart N hpos b)).map
        (lpsOriginalComplexNormalChartDifferentialRestrictionIso N hpos b).hom) =
    schemeRestrictedDifferentialSheafDerivation (lpsOriginalComplexNormalGluedChartMap N hpos b)
      (CommRingCat.of ℂ) c := by sorry
