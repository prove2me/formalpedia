-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalInfinityLaurentAffineCoefficientSquare
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalInfinityLaurentAffineCoefficientSquare
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:38:48.442376+00:00
-- url     : https://prove2.me/theorems/bc44351d-c865-4096-8501-f16ef9b4c392
-- title:
--   Tanner Lifted Product: lps Original Infinity Laurent Affine Coefficient Square
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Infinity Laurent Affine Coefficient Square property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNativeGlobalDifferentials.lean#L64-L69
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNativeGlobalDifferentials.lean#L64-L69

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
attribute [local instance] QEC.Coding.TannerLiftedProduct.originalZeroLaurentRestrictionOpen
attribute [local instance] QEC.Coding.TannerLiftedProduct.originalInfinityLaurentRestrictionOpen

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalInfinityLaurentAffineCoefficientSquare :
    (CommRingCat.ofHom (algebraMap ℂ I) : CommRingCat.of ℂ ⟶ CommRingCat.of I) ≫
      CommRingCat.ofHom (lpsOriginalComplexNormalInfinityToLaurent N hpos) =
        CommRingCat.ofHom (algebraMap ℂ T) := by sorry
