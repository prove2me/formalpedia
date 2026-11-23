-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SheafLES___apply_7b49c5df3cf6
-- name    : P2M_GlobalTheory_SheafLES___apply_7b49c5df3cf6
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:18:15.724905+00:00
-- url     : https://prove2.me/theorems/a0f9f256-db59-41f0-9951-9d6881f07269
-- title:
--   P2 M Global Theory Sheaf LES   apply 7b49c5df3cf6: P2 M Global Theory Sheaf LES   apply 7b49c5df3cf6
-- statement:
--   The P2 M Global Theory Sheaf LES   apply 7b49c5df3cf6 construction uses the P2 M Global Theory Sheaf LES   apply 7b49c5df3cf6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L152-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L152-L153

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

theorem P2M_GlobalTheory_SheafLES___apply_7b49c5df3cf6 (n : ℕ) (U : C) (x : Ext.{w'} ((freeYoneda J).obj U) S.X₃ n) :
    δ hS n U x = x.comp hS.extClass rfl := by sorry

alias «GlobalTheory».«SheafLES».«δ_apply» := P2M_GlobalTheory_SheafLES___apply_7b49c5df3cf6
