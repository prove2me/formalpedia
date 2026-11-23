-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SheafLES_exact__a6249fcd4aae
-- name    : P2M_GlobalTheory_SheafLES_exact__a6249fcd4aae
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:00.686339+00:00
-- url     : https://prove2.me/theorems/d26eeb8c-fc39-4f7a-b964-bcf14f946482
-- title:
--   P2 M Global Theory Sheaf LES exact  a6249fcd4aae: P2 M Global Theory Sheaf LES exact  a6249fcd4aae
-- statement:
--   The P2 M Global Theory Sheaf LES exact  a6249fcd4aae construction uses the P2 M Global Theory Sheaf LES exact  a6249fcd4aae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L157-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L157-L159

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

theorem P2M_GlobalTheory_SheafLES_exact__a6249fcd4aae (n : ℕ) (U : C) : Function.Exact (map.{w'} S.f n U) (map.{w'} S.g n U) := by sorry

alias «GlobalTheory».«SheafLES».«exact₂» := P2M_GlobalTheory_SheafLES_exact__a6249fcd4aae
