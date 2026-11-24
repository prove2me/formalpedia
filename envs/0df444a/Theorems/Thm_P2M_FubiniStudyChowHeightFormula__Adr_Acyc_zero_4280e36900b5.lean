-- Prove2me | Theorems.Thm_P2M_FubiniStudyChowHeightFormula__Adr_Acyc_zero_4280e36900b5
-- name    : P2M_FubiniStudyChowHeightFormula__Adr_Acyc_zero_4280e36900b5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:49:25.561801+00:00
-- url     : https://prove2.me/theorems/96b13c59-d57d-416d-a7ec-ebca85230b72
-- title:
--   P2 M Fubini Study Chow Height Formula  Adr Acyc zero 4280e36900b5: P2 M Fubini Study Chow Height Formula  Adr Acyc zero 4280e36900b5
-- statement:
--   The P2 M Fubini Study Chow Height Formula  Adr Acyc zero 4280e36900b5 construction uses the P2 M Fubini Study Chow Height Formula  Adr Acyc zero 4280e36900b5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AbelianHeightsDuality/DividedPowerAlgebras/AcycOfCoprod.lean#L87-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AbelianHeightsDuality/DividedPowerAlgebras/AcycOfCoprod.lean#L87-L91

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
  {G : C' ⥤ C} {T : C}

theorem P2M_FubiniStudyChowHeightFormula__Adr_Acyc_zero_4280e36900b5 (h : Acyc R (CostructuredArrow G T)) (M : CommAlgCat.{0} R) (g : ∀ S, (G.obj S ⟶ T) → M)
    (hg : ∀ S S' (ψ : S ⟶ S') (c : G.obj S' ⟶ T), g S (G.map ψ ≫ c) = g S' c) : ∃ m, ∀ S c, g S c = m := by sorry

alias «FubiniStudyChowHeightFormula₂».«Adr».«Acyc».«zero» := P2M_FubiniStudyChowHeightFormula__Adr_Acyc_zero_4280e36900b5
