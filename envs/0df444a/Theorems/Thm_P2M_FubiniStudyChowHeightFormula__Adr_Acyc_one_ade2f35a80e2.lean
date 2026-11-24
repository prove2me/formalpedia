-- Prove2me | Theorems.Thm_P2M_FubiniStudyChowHeightFormula__Adr_Acyc_one_ade2f35a80e2
-- name    : P2M_FubiniStudyChowHeightFormula__Adr_Acyc_one_ade2f35a80e2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:49:29.083458+00:00
-- url     : https://prove2.me/theorems/0ba45c2e-140b-4af9-b54b-d309bbf0ad9c
-- title:
--   P2 M Fubini Study Chow Height Formula  Adr Acyc one ade2f35a80e2: P2 M Fubini Study Chow Height Formula  Adr Acyc one ade2f35a80e2
-- statement:
--   The P2 M Fubini Study Chow Height Formula  Adr Acyc one ade2f35a80e2 construction uses the P2 M Fubini Study Chow Height Formula  Adr Acyc one ade2f35a80e2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AbelianHeightsDuality/DividedPowerAlgebras/AcycOfCoprod.lean#L93-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AbelianHeightsDuality/DividedPowerAlgebras/AcycOfCoprod.lean#L93-L105

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

theorem P2M_FubiniStudyChowHeightFormula__Adr_Acyc_one_ade2f35a80e2 (h : Acyc R (CostructuredArrow G T)) (M : CommAlgCat.{0} R)
    (f : ∀ S S', (S ⟶ S') → (G.obj S' ⟶ T) → M)
    (hf : ∀ S S' S'' (φ : S ⟶ S') (ψ : S' ⟶ S'') (c : G.obj S'' ⟶ T),
      f S S'' (φ ≫ ψ) c = f S S' φ (G.map ψ ≫ c) + f S' S'' ψ c) :
    ∃ v : ∀ S, (G.obj S ⟶ T) → M, ∀ S S' (ψ : S ⟶ S') (c : G.obj S' ⟶ T), f S S' ψ c = v S' c - v S (G.map ψ ≫ c) := by sorry

alias «FubiniStudyChowHeightFormula₂».«Adr».«Acyc».«one» := P2M_FubiniStudyChowHeightFormula__Adr_Acyc_one_ade2f35a80e2
