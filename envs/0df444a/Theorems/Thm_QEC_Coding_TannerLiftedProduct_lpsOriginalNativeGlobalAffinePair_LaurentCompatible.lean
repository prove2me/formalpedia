-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNativeGlobalAffinePair_LaurentCompatible
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalNativeGlobalAffinePair_LaurentCompatible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:59:21.777918+00:00
-- url     : https://prove2.me/theorems/18ebc8b4-a8b3-4537-8300-cd7005cb39da
-- title:
--   Tanner Lifted Product: lps Original Native Global Affine Pair Laurent Compatible
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Native Global Affine Pair Laurent Compatible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNativeGlobalRegularity.lean#L157-L176
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNativeGlobalRegularity.lean#L157-L176

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeGlobalDifferentials
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeGlobalRegularity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open CategoryTheory _root_.AlgebraicGeometry Opposite QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open scoped _root_.AlgebraicGeometry MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
local notation "R" => lpsOriginalComplexNormalZeroChart N hpos
local notation "I" => lpsOriginalComplexNormalInfinityChart N hpos
local notation "T" => lpsOriginalComplexNormalLaurentChart N hpos
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "Omega" => lpsOriginalComplexNormalDifferentialSheaf N hpos
local notation "X" => lpsOriginalComplexNormalGluedScheme N hpos
local notation "c" => lpsOriginalComplexNormalGlobalConstantMap N hpos
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
attribute [local instance] originalNativeGlobalZeroOpen originalNativeGlobalInfinityOpen
attribute [local instance]
  LPSOriginalAffineKaehlerCompatibilityDictionary001
  LPSOriginalAffineKaehlerCompatibilityDictionary002
  LPSOriginalAffineKaehlerCompatibilityDictionary003
  LPSOriginalAffineKaehlerCompatibilityDictionary004
  LPSOriginalAffineKaehlerCompatibilityDictionary011
  LPSOriginalAffineKaehlerCompatibilityDictionary012
  LPSOriginalAffineKaehlerCompatibilityDictionary013
  LPSOriginalAffineKaehlerCompatibilityDictionary014
  LPSOriginalAffineKaehlerCompatibilityDictionary023
  LPSOriginalAffineKaehlerCompatibilityDictionary024
  LPSOriginalAffineKaehlerCompatibilityDictionary025
  LPSOriginalAffineKaehlerCompatibilityDictionary026
attribute [local instance] LPSOriginalAffineKaehlerCompatibilityDictionary027
  LPSOriginalAffineKaehlerCompatibilityDictionary034
  LPSOriginalAffineKaehlerCompatibilityDictionary035
  LPSOriginalAffineKaehlerCompatibilityDictionary036
  LPSOriginalAffineKaehlerCompatibilityDictionary037
  LPSOriginalAffineKaehlerCompatibilityDictionary041
  LPSOriginalAffineKaehlerCompatibilityDictionary050

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalNativeGlobalAffinePair_LaurentCompatible (z : Γ(Omega, ⊤)) :
    KaehlerDifferential.map ℂ ℂ R T (lpsOriginalNativeGlobalAffinePair N hpos z).1 =
      KaehlerDifferential.map ℂ ℂ I T (lpsOriginalNativeGlobalAffinePair N hpos z).2 := by sorry
