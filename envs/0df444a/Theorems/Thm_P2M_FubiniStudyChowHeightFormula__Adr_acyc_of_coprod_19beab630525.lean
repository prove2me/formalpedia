-- Prove2me | Theorems.Thm_P2M_FubiniStudyChowHeightFormula__Adr_acyc_of_coprod_19beab630525
-- name    : P2M_FubiniStudyChowHeightFormula__Adr_acyc_of_coprod_19beab630525
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:05:32.156427+00:00
-- url     : https://prove2.me/theorems/78779f89-c9f5-4b89-ae0c-6142e4171f38
-- title:
--   P2 M Fubini Study Chow Height Formula  Adr acyc of coprod 19beab630525: P2 M Fubini Study Chow Height Formula  Adr acyc of coprod 19beab630525
-- statement:
--   The P2 M Fubini Study Chow Height Formula  Adr acyc of coprod 19beab630525 construction uses the P2 M Fubini Study Chow Height Formula  Adr acyc of coprod 19beab630525 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AbelianHeightsDuality/DividedPowerAlgebras/AcycOfCoprod.lean#L65-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AbelianHeightsDuality/DividedPowerAlgebras/AcycOfCoprod.lean#L65-L78

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

theorem P2M_FubiniStudyChowHeightFormula__Adr_acyc_of_coprod_19beab630525 (d : D) (P : D → D) (i : ∀ a, a ⟶ P a) (j : ∀ a, d ⟶ P a)
    (h : ∀ a b (φ : a ⟶ P b), ∃! ψ : P a ⟶ P b, i a ≫ ψ = φ ∧ j a ≫ ψ = j b) : Acyc R D := by sorry

alias «FubiniStudyChowHeightFormula₂».«Adr».«acyc_of_coprod» := P2M_FubiniStudyChowHeightFormula__Adr_acyc_of_coprod_19beab630525
