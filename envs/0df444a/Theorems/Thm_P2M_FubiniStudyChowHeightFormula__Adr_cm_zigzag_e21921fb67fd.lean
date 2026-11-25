-- Prove2me | Theorems.Thm_P2M_FubiniStudyChowHeightFormula__Adr_cm_zigzag_e21921fb67fd
-- name    : P2M_FubiniStudyChowHeightFormula__Adr_cm_zigzag_e21921fb67fd
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:02:07.964808+00:00
-- url     : https://prove2.me/theorems/42fef597-bdf8-409a-9e0f-841f0cde218d
-- title:
--   P2 M Fubini Study Chow Height Formula  Adr cm zigzag e21921fb67fd: P2 M Fubini Study Chow Height Formula  Adr cm zigzag e21921fb67fd
-- statement:
--   The P2 M Fubini Study Chow Height Formula  Adr cm zigzag e21921fb67fd construction uses the P2 M Fubini Study Chow Height Formula  Adr cm zigzag e21921fb67fd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AbelianHeightsDuality/DividedPowerAlgebras/AcycOfCoprod.lean#L29-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AbelianHeightsDuality/DividedPowerAlgebras/AcycOfCoprod.lean#L29-L45

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
variable {R : Type} [CommRing R] {D : Type u} [Category.{v} D]

theorem P2M_FubiniStudyChowHeightFormula__Adr_cm_zigzag_e21921fb67fd (M : CommAlgCat.{0} R) {G G' : D ⥤ D} (h : Zigzag G G') :
    (∀ g : D → M, (∀ a b (_ : a ⟶ b), g b = g a) → ∀ a, g (G.obj a) = g (G'.obj a)) ∧
    (∀ c, (cm M G).pull1 c = (cm M G').pull1 c) ∧ ∀ c, (cm M G).pull2 c = (cm M G').pull2 c := by sorry

alias «FubiniStudyChowHeightFormula₂».«Adr».«cm_zigzag» := P2M_FubiniStudyChowHeightFormula__Adr_cm_zigzag_e21921fb67fd
