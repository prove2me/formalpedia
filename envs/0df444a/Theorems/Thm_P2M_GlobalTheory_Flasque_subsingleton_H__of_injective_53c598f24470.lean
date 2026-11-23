-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Flasque_subsingleton_H__of_injective_53c598f24470
-- name    : P2M_GlobalTheory_Flasque_subsingleton_H__of_injective_53c598f24470
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:18:02.576443+00:00
-- url     : https://prove2.me/theorems/d611dbe9-ef35-42ca-8435-da3f1e8454dd
-- title:
--   P2 M Global Theory Flasque subsingleton H  of injective 53c598f24470: P2 M Global Theory Flasque subsingleton H  of injective 53c598f24470
-- statement:
--   The P2 M Global Theory Flasque subsingleton H  of injective 53c598f24470 construction uses the P2 M Global Theory Flasque subsingleton H  of injective 53c598f24470 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CohomologyPresheafFunctorMapAppApply.lean#L92-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CohomologyPresheafFunctorMapAppApply.lean#L92-L94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Abelian Opposite Limits TopologicalSpace
universe w v u
open GlobalTheory
open GlobalTheory.Flasque
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}]
variable {J}
variable [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
open CategoryTheory Abelian Opposite Limits TopologicalSpace
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}]
variable {J}
variable [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

theorem P2M_GlobalTheory_Flasque_subsingleton_H__of_injective_53c598f24470 (I : Sheaf J AddCommGrpCat.{v}) [Injective I]
    (n : ℕ) (U : C) : Subsingleton (I.H' (n + 1) U) := by sorry

alias «GlobalTheory».«Flasque».«subsingleton_H'_of_injective» := P2M_GlobalTheory_Flasque_subsingleton_H__of_injective_53c598f24470
