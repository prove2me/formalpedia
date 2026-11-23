-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SheafLES_exact__24269ba80ece
-- name    : P2M_GlobalTheory_SheafLES_exact__24269ba80ece
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:04:51.917044+00:00
-- url     : https://prove2.me/theorems/064a4417-d384-4f97-8a2b-d1c0d2b51415
-- title:
--   P2 M Global Theory Sheaf LES exact  24269ba80ece: P2 M Global Theory Sheaf LES exact  24269ba80ece
-- statement:
--   The P2 M Global Theory Sheaf LES exact  24269ba80ece construction uses the P2 M Global Theory Sheaf LES exact  24269ba80ece property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L161-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L161-L163

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

theorem P2M_GlobalTheory_SheafLES_exact__24269ba80ece (n : ℕ) (U : C) : Function.Exact (map.{w'} S.g n U) (δ.{w'} hS n U) := by sorry

alias «GlobalTheory».«SheafLES».«exact₃» := P2M_GlobalTheory_SheafLES_exact__24269ba80ece
