-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNativeGlobalAffinePair_eq_iff
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalNativeGlobalAffinePair_eq_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:41:41.080757+00:00
-- url     : https://prove2.me/theorems/c6e1be13-267d-4009-b255-f2722c0cce89
-- title:
--   Tanner Lifted Product: lps Original Native Global Affine Pair eq iff
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Native Global Affine Pair eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNativeGlobalDifferentials.lean#L243-L252
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNativeGlobalDifferentials.lean#L243-L252

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
local notation "Omega" => lpsOriginalComplexNormalDifferentialSheaf N hpos
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
local notation "U" => Functor.obj (Scheme.Hom.opensFunctor
  (lpsOriginalComplexNormalGluedChartMap N hpos false)) ⊤
local notation "V" => Functor.obj (Scheme.Hom.opensFunctor
  (lpsOriginalComplexNormalGluedChartMap N hpos true)) ⊤

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalNativeGlobalAffinePair_eq_iff (z : Γ(Omega, ⊤))
    (a : KaehlerDifferential ℂ R) (b : KaehlerDifferential ℂ I) :
    lpsOriginalNativeGlobalAffinePair N hpos z = (a, b) ↔
    (Omega).presheaf.map (homOfLE le_top : U ⟶ ⊤).op z =
      (lpsOriginalZeroImageFromKaehler N hpos).hom a ∧
    (Omega).presheaf.map (homOfLE le_top : V ⟶ ⊤).op z =
      (lpsOriginalInfinityImageFromKaehler N hpos).hom b := by sorry
