-- Prove2me | Theorems.Thm_P2M_FubiniStudyChowHeightFormula__Adr_qa2_dcbabdd33386
-- name    : P2M_FubiniStudyChowHeightFormula__Adr_qa2_dcbabdd33386
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:02:08.092594+00:00
-- url     : https://prove2.me/theorems/99bc18d6-316c-4623-a80b-77c03891722d
-- title:
--   P2 M Fubini Study Chow Height Formula  Adr qa2 dcbabdd33386: P2 M Fubini Study Chow Height Formula  Adr qa2 dcbabdd33386
-- statement:
--   The P2 M Fubini Study Chow Height Formula  Adr qa2 dcbabdd33386 construction uses the P2 M Fubini Study Chow Height Formula  Adr qa2 dcbabdd33386 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AbelianHeightsDuality/DividedPowerAlgebras/AcycOfCoprod.lean#L192-L275
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AbelianHeightsDuality/DividedPowerAlgebras/AcycOfCoprod.lean#L192-L275

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Definitions.Def_Development_WeilBound_CoreStatements_AbelianHeightsDuality_DividedPowerAlgebras_AcycOfCoprod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory GlobalTheory.CatCoh
open FubiniStudyChowHeightFormula₂ FubiniStudyChowHeightFormula₂.Adr
universe v u v' u'
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']

theorem P2M_FubiniStudyChowHeightFormula__Adr_qa2_dcbabdd33386 (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) (h : ∀ T, Acyc R (CostructuredArrow G T)) :
    Function.Bijective (CoefMap.restrict F G).pull2 := by sorry

alias «FubiniStudyChowHeightFormula₂».«Adr».«qa2» := P2M_FubiniStudyChowHeightFormula__Adr_qa2_dcbabdd33386
