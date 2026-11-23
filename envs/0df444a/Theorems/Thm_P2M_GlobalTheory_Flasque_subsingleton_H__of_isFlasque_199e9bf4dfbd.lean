-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Flasque_subsingleton_H__of_isFlasque_199e9bf4dfbd
-- name    : P2M_GlobalTheory_Flasque_subsingleton_H__of_isFlasque_199e9bf4dfbd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:04:22.972426+00:00
-- url     : https://prove2.me/theorems/b84e03f0-0a4a-4e5b-afa5-18b7862a599c
-- title:
--   P2 M Global Theory Flasque subsingleton H  of is Flasque 199e9bf4dfbd: P2 M Global Theory Flasque subsingleton H  of is Flasque 199e9bf4dfbd
-- statement:
--   The P2 M Global Theory Flasque subsingleton H  of is Flasque 199e9bf4dfbd construction uses the P2 M Global Theory Flasque subsingleton H  of is Flasque 199e9bf4dfbd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CohomologyPresheafFunctorMapAppApply.lean#L322-L352
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CohomologyPresheafFunctorMapAppApply.lean#L322-L352

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
variable {X : TopCat.{u}}
variable [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
open CategoryTheory Abelian Opposite Limits TopologicalSpace
variable {X : TopCat.{u}}
variable [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

theorem P2M_GlobalTheory_Flasque_subsingleton_H__of_isFlasque_199e9bf4dfbd (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    [hF : F.IsFlasque] (n : ℕ) (U : Opens X) : Subsingleton (F.H' (n + 1) U) := by sorry

alias «GlobalTheory».«Flasque».«subsingleton_H'_of_isFlasque» := P2M_GlobalTheory_Flasque_subsingleton_H__of_isFlasque_199e9bf4dfbd
