-- Prove2me | Theorems.Thm_P2M_FubiniStudyChowHeightFormula__Adr_Acyc_two_37305c98b3e1
-- name    : P2M_FubiniStudyChowHeightFormula__Adr_Acyc_two_37305c98b3e1
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:02:22.634249+00:00
-- url     : https://prove2.me/theorems/d20863ad-7348-4882-bcfa-e46320dabd89
-- title:
--   P2 M Fubini Study Chow Height Formula  Adr Acyc two 37305c98b3e1: P2 M Fubini Study Chow Height Formula  Adr Acyc two 37305c98b3e1
-- statement:
--   The P2 M Fubini Study Chow Height Formula  Adr Acyc two 37305c98b3e1 construction uses the P2 M Fubini Study Chow Height Formula  Adr Acyc two 37305c98b3e1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AbelianHeightsDuality/DividedPowerAlgebras/AcycOfCoprod.lean#L107-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AbelianHeightsDuality/DividedPowerAlgebras/AcycOfCoprod.lean#L107-L130

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

theorem P2M_FubiniStudyChowHeightFormula__Adr_Acyc_two_37305c98b3e1 (h : Acyc R (CostructuredArrow G T)) (M : CommAlgCat.{0} R)
    (z : ∀ S S' S'', (S ⟶ S') → (S' ⟶ S'') → (G.obj S'' ⟶ T) → M)
    (hz : ∀ S S' S'' S''' (φ : S ⟶ S') (ψ : S' ⟶ S'') (χ : S'' ⟶ S''') (c : G.obj S''' ⟶ T),
      z S S' S'' φ ψ (G.map χ ≫ c) + z S S'' S''' (φ ≫ ψ) χ c = z S S' S''' φ (ψ ≫ χ) c + z S' S'' S''' ψ χ c) :
    ∃ w : ∀ S S', (S ⟶ S') → (G.obj S' ⟶ T) → M, ∀ S S' S'' (φ : S ⟶ S') (ψ : S' ⟶ S'') (c : G.obj S'' ⟶ T),
      z S S' S'' φ ψ c = w S S' φ (G.map ψ ≫ c) - w S S'' (φ ≫ ψ) c + w S' S'' ψ c := by sorry

alias «FubiniStudyChowHeightFormula₂».«Adr».«Acyc».«two» := P2M_FubiniStudyChowHeightFormula__Adr_Acyc_two_37305c98b3e1
