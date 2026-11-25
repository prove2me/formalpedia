-- Prove2me | Theorems.Thm_P2M_FubiniStudyChowHeightFormula__Adr_qa1_7c8b1fea16fe
-- name    : P2M_FubiniStudyChowHeightFormula__Adr_qa1_7c8b1fea16fe
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:02:21.991858+00:00
-- url     : https://prove2.me/theorems/be3f4313-acdf-4ec5-aefb-2a0feefeb6fb
-- title:
--   P2 M Fubini Study Chow Height Formula  Adr qa1 7c8b1fea16fe: P2 M Fubini Study Chow Height Formula  Adr qa1 7c8b1fea16fe
-- statement:
--   The P2 M Fubini Study Chow Height Formula  Adr qa1 7c8b1fea16fe construction uses the P2 M Fubini Study Chow Height Formula  Adr qa1 7c8b1fea16fe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AbelianHeightsDuality/DividedPowerAlgebras/AcycOfCoprod.lean#L138-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AbelianHeightsDuality/DividedPowerAlgebras/AcycOfCoprod.lean#L138-L190

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

theorem P2M_FubiniStudyChowHeightFormula__Adr_qa1_7c8b1fea16fe (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) (h : ∀ T, Acyc R (CostructuredArrow G T)) :
    Function.Bijective (CoefMap.restrict F G).pull1 := by sorry

alias «FubiniStudyChowHeightFormula₂».«Adr».«qa1» := P2M_FubiniStudyChowHeightFormula__Adr_qa1_7c8b1fea16fe
