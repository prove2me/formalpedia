-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SheafLES_subsingleton__zero_1933a20f9277
-- name    : P2M_GlobalTheory_SheafLES_subsingleton__zero_1933a20f9277
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:09:00.616695+00:00
-- url     : https://prove2.me/theorems/10afe187-ff3e-47d3-b6b6-02a760e62f2d
-- title:
--   P2 M Global Theory Sheaf LES subsingleton  zero 1933a20f9277: P2 M Global Theory Sheaf LES subsingleton  zero 1933a20f9277
-- statement:
--   The P2 M Global Theory Sheaf LES subsingleton  zero 1933a20f9277 construction uses the P2 M Global Theory Sheaf LES subsingleton  zero 1933a20f9277 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L262-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L262-L264

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

theorem P2M_GlobalTheory_SheafLES_subsingleton__zero_1933a20f9277 (U : C) (h₂ : Subsingleton (Sheaf.H'.{w'} S.X₂ 0 U)) :
    Subsingleton (Sheaf.H'.{w'} S.X₁ 0 U) := by sorry

alias «GlobalTheory».«SheafLES».«subsingleton₁_zero» := P2M_GlobalTheory_SheafLES_subsingleton__zero_1933a20f9277
