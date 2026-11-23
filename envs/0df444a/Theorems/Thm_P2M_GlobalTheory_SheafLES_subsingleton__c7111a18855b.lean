-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SheafLES_subsingleton__c7111a18855b
-- name    : P2M_GlobalTheory_SheafLES_subsingleton__c7111a18855b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:08:45.63092+00:00
-- url     : https://prove2.me/theorems/294549d8-a0df-43a0-bc55-bfc4d8d15377
-- title:
--   P2 M Global Theory Sheaf LES subsingleton  c7111a18855b: P2 M Global Theory Sheaf LES subsingleton  c7111a18855b
-- statement:
--   The P2 M Global Theory Sheaf LES subsingleton  c7111a18855b construction uses the P2 M Global Theory Sheaf LES subsingleton  c7111a18855b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L253-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L253-L255

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

theorem P2M_GlobalTheory_SheafLES_subsingleton__c7111a18855b (n : ℕ) (U : C) (h₂ : Subsingleton (Sheaf.H'.{w'} S.X₂ n U))
    (h₁ : Subsingleton (Sheaf.H'.{w'} S.X₁ (n + 1) U)) : Subsingleton (Sheaf.H'.{w'} S.X₃ n U) := by sorry

alias «GlobalTheory».«SheafLES».«subsingleton₃» := P2M_GlobalTheory_SheafLES_subsingleton__c7111a18855b
