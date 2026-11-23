-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SheafLES_exact__5aa7b67be2da
-- name    : P2M_GlobalTheory_SheafLES_exact__5aa7b67be2da
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:05:09.930612+00:00
-- url     : https://prove2.me/theorems/779d30fb-3ece-4e65-86a4-23b57f0ac341
-- title:
--   P2 M Global Theory Sheaf LES exact  5aa7b67be2da: P2 M Global Theory Sheaf LES exact  5aa7b67be2da
-- statement:
--   The P2 M Global Theory Sheaf LES exact  5aa7b67be2da construction uses the P2 M Global Theory Sheaf LES exact  5aa7b67be2da property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L165-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L165-L167

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

theorem P2M_GlobalTheory_SheafLES_exact__5aa7b67be2da (n : ℕ) (U : C) : Function.Exact (δ.{w'} hS n U) (map.{w'} S.f (n + 1) U) := by sorry

alias «GlobalTheory».«SheafLES».«exact₁» := P2M_GlobalTheory_SheafLES_exact__5aa7b67be2da
