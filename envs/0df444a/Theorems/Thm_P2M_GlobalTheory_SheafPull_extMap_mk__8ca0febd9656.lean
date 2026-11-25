-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SheafPull_extMap_mk__8ca0febd9656
-- name    : P2M_GlobalTheory_SheafPull_extMap_mk__8ca0febd9656
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:08:46.271153+00:00
-- url     : https://prove2.me/theorems/55a9acd5-ba4e-49dc-8058-ee3a83685557
-- title:
--   P2 M Global Theory Sheaf Pull ext Map mk  8ca0febd9656: P2 M Global Theory Sheaf Pull ext Map mk  8ca0febd9656
-- statement:
--   The P2 M Global Theory Sheaf Pull ext Map mk  8ca0febd9656 construction uses the P2 M Global Theory Sheaf Pull ext Map mk  8ca0febd9656 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/FreeYonedaHomEquivFreeToPullbackComp.lean#L31-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/FreeYonedaHomEquivFreeToPullbackComp.lean#L31-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FreeYonedaHomEquivFreeToPullbackComp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Abelian Opposite Limits TopologicalSpace
universe w w' w'' v u u₁ v₁ u₂ v₂
noncomputable section
open GlobalTheory
open GlobalTheory.SheafPull
variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasExt.{w} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasExt.{w'} B]
  (Φ : A ⥤ B) [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]

theorem P2M_GlobalTheory_SheafPull_extMap_mk__8ca0febd9656 {Z F : A} {Z' G : B} (a : Z' ⟶ Φ.obj Z) (b : Φ.obj F ⟶ G) (g : Z ⟶ F) :
    extMap.{w, w'} Φ a b 0 (Ext.mk₀ g) = Ext.mk₀ (a ≫ Φ.map g ≫ b) := by sorry

alias «GlobalTheory».«SheafPull».«extMap_mk₀» := P2M_GlobalTheory_SheafPull_extMap_mk__8ca0febd9656
