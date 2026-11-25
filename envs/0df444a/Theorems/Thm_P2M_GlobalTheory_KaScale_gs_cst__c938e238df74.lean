-- Prove2me | Theorems.Thm_P2M_GlobalTheory_KaScale_gs_cst__c938e238df74
-- name    : P2M_GlobalTheory_KaScale_gs_cst__c938e238df74
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:07:37.070622+00:00
-- url     : https://prove2.me/theorems/4f694e71-69d1-4d65-9d6e-aec7a2b7726a
-- title:
--   P2 M Global Theory Ka Scale gs cst  c938e238df74: P2 M Global Theory Ka Scale gs cst  c938e238df74
-- statement:
--   The P2 M Global Theory Ka Scale gs cst  c938e238df74 construction uses the P2 M Global Theory Ka Scale gs cst  c938e238df74 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IsSquareDetComparisonScaleSec.lean#L118-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IsSquareDetComparisonScaleSec.lean#L118-L120

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_KaFormHomogeneous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsLieBasisIffIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SubsingletonPrimeSpectrum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsSquareDetComparisonScaleSec
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isLieComb_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isTan_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open ReciprocityTheory.ChartRestriction.G.Chart (sp fstD scaleD prodPts isTan_iff isLieComb_iff comp_one' isTan_mul isTan_one
  isTan_scale)
open GlobalTheory.UnifDifferential GlobalTheory.SqZero
noncomputable section
open GlobalTheory GlobalTheory.KaScale

theorem P2M_GlobalTheory_KaScale_gs_cst__c938e238df74 {K : Type} [CommRing K] {Y : Scheme.{0}} (p : Y ⟶ Sp K) (y : Y) (a : K) :
    gs (𝟙 Y) y ⊤ (AbLaw.cst p ⊤ a) = cS p y a := by sorry

alias «GlobalTheory».«KaScale».«gs_cst'» := P2M_GlobalTheory_KaScale_gs_cst__c938e238df74
