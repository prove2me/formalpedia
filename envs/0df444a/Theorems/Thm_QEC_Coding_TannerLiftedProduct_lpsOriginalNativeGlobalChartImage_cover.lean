-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNativeGlobalChartImage_cover
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalNativeGlobalChartImage_cover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:38:05.311691+00:00
-- url     : https://prove2.me/theorems/1fbbc126-2083-4a0a-9267-052df4e7adb0
-- title:
--   Tanner Lifted Product: lps Original Native Global Chart Image cover
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Native Global Chart Image cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNativeGlobalDifferentials.lean#L151-L153
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNativeGlobalDifferentials.lean#L151-L153

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineChartDescent
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialImages
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialSheaf
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAffineKaehlerCompatibility
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeGlobalDifferentials
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open CategoryTheory _root_.AlgebraicGeometry Opposite QEC.Coding.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N)
local notation "R" => lpsOriginalComplexNormalZeroChart N hpos
local notation "I" => lpsOriginalComplexNormalInfinityChart N hpos
local notation "T" => lpsOriginalComplexNormalLaurentChart N hpos
local notation "X" => lpsOriginalComplexNormalGluedScheme N hpos
local notation "c" => lpsOriginalComplexNormalGlobalConstantMap N hpos
local notation "Omega" => lpsOriginalComplexNormalDifferentialSheaf N hpos
local notation "f0" => lpsOriginalComplexNormalGluedChartMap N hpos false
local notation "f1" => lpsOriginalComplexNormalGluedChartMap N hpos true
local notation "q0" => CommRingCat.ofHom (lpsOriginalComplexNormalZeroToLaurent N hpos)
local notation "q1" => CommRingCat.ofHom (lpsOriginalComplexNormalInfinityToLaurent N hpos)
attribute [local instance] lpsOriginalZeroChartDifferentialAlgebra
  lpsOriginalInfinityChartDifferentialAlgebra lpsOriginalZeroChartDifferentialSMul
  lpsOriginalZeroChartDifferentialModule lpsOriginalZeroChartDifferentialSMulComm
  lpsOriginalZeroChartOmegaSMul lpsOriginalZeroChartOmegaModule
  lpsOriginalInfinityChartDifferentialSMul lpsOriginalInfinityChartDifferentialModule
  lpsOriginalInfinityChartDifferentialSMulComm lpsOriginalInfinityChartOmegaSMul
  lpsOriginalInfinityChartOmegaModule
  LPSOriginalAffineKaehlerCompatibilityDictionary028
  LPSOriginalAffineKaehlerCompatibilityDictionary029
  LPSOriginalAffineKaehlerCompatibilityDictionary030
  LPSOriginalAffineKaehlerCompatibilityDictionary031
  LPSOriginalAffineKaehlerCompatibilityDictionary032
  LPSOriginalAffineKaehlerCompatibilityDictionary033
  LPSOriginalAffineKaehlerCompatibilityDictionary038
  LPSOriginalAffineKaehlerCompatibilityDictionary039
  LPSOriginalAffineKaehlerCompatibilityDictionary040
  LPSOriginalAffineKaehlerCompatibilityDictionary042
  LPSOriginalAffineKaehlerCompatibilityDictionary043
  LPSOriginalAffineKaehlerCompatibilityDictionary044
  LPSOriginalAffineKaehlerCompatibilityDictionary045
  LPSOriginalAffineKaehlerCompatibilityDictionary047
  LPSOriginalAffineKaehlerCompatibilityDictionary048
  LPSOriginalAffineKaehlerCompatibilityDictionary049
  LPSOriginalAffineKaehlerCompatibilityDictionary051
  LPSOriginalAffineKaehlerCompatibilityDictionary052
  LPSOriginalAffineKaehlerCompatibilityDictionary053
  LPSOriginalAffineKaehlerCompatibilityDictionary054
attribute [local instance] originalZeroLaurentRestrictionOpen originalInfinityLaurentRestrictionOpen
attribute [local instance] QEC.Coding.TannerLiftedProduct.originalNativeGlobalZeroOpen
attribute [local instance] QEC.Coding.TannerLiftedProduct.originalNativeGlobalInfinityOpen
attribute [local instance] QEC.Coding.TannerLiftedProduct.originalNativeGlobalLaurentCompositeOpen
local notation "U" => Functor.obj (Scheme.Hom.opensFunctor (f0)) ⊤
local notation "V" => Functor.obj (Scheme.Hom.opensFunctor (f1)) ⊤
local notation "W" => Functor.obj (Scheme.Hom.opensFunctor (Spec.map (q0) ≫ (f0))) ⊤
omit [NeZero N]

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalNativeGlobalChartImage_cover : U ⊔ V = ⊤ := by sorry
