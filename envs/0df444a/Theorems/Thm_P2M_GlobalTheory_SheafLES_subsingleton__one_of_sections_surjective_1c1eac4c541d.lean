-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SheafLES_subsingleton__one_of_sections_surjective_1c1eac4c541d
-- name    : P2M_GlobalTheory_SheafLES_subsingleton__one_of_sections_surjective_1c1eac4c541d
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:08:50.746257+00:00
-- url     : https://prove2.me/theorems/251ba7fa-49b4-4824-b1ee-205a4b6367c9
-- title:
--   P2 M Global Theory Sheaf LES subsingleton  one of sections surjective 1c1eac4c541d: P2 M Global Theory Sheaf LES subsingleton  one of sections surjective 1c1eac4c541d
-- statement:
--   The P2 M Global Theory Sheaf LES subsingleton  one of sections surjective 1c1eac4c541d construction uses the P2 M Global Theory Sheaf LES subsingleton  one of sections surjective 1c1eac4c541d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L266-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L266-L269

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe w' v u
open CategoryTheory Limits Abelian Opposite
noncomputable section
open GlobalTheory
open GlobalTheory.SheafLES
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}]
variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]
variable {S : ShortComplex (Sheaf J AddCommGrpCat.{v})} (hS : S.ShortExact)
include hS

theorem P2M_GlobalTheory_SheafLES_subsingleton__one_of_sections_surjective_1c1eac4c541d (U : C)
    (h : Function.Surjective (S.g.hom.app (op U)))
    (h₂ : Subsingleton (Sheaf.H'.{w'} S.X₂ 1 U)) : Subsingleton (Sheaf.H'.{w'} S.X₁ 1 U) := by sorry

alias «GlobalTheory».«SheafLES».«subsingleton₁_one_of_sections_surjective» := P2M_GlobalTheory_SheafLES_subsingleton__one_of_sections_surjective_1c1eac4c541d
