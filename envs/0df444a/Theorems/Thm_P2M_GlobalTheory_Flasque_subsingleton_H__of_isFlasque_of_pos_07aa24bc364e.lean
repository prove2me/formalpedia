-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Flasque_subsingleton_H__of_isFlasque_of_pos_07aa24bc364e
-- name    : P2M_GlobalTheory_Flasque_subsingleton_H__of_isFlasque_of_pos_07aa24bc364e
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:05:59.041007+00:00
-- url     : https://prove2.me/theorems/db3ac377-f50d-4830-98c5-bee88261194a
-- title:
--   P2 M Global Theory Flasque subsingleton H  of is Flasque of pos 07aa24bc364e: P2 M Global Theory Flasque subsingleton H  of is Flasque of pos 07aa24bc364e
-- statement:
--   The P2 M Global Theory Flasque subsingleton H  of is Flasque of pos 07aa24bc364e construction uses the P2 M Global Theory Flasque subsingleton H  of is Flasque of pos 07aa24bc364e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CohomologyPresheafFunctorMapAppApply.lean#L357-L360
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CohomologyPresheafFunctorMapAppApply.lean#L357-L360

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

theorem P2M_GlobalTheory_Flasque_subsingleton_H__of_isFlasque_of_pos_07aa24bc364e (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    [F.IsFlasque] {n : ℕ} (hn : 0 < n) (U : Opens X) : Subsingleton (F.H' n U) := by sorry

alias «GlobalTheory».«Flasque».«subsingleton_H'_of_isFlasque_of_pos» := P2M_GlobalTheory_Flasque_subsingleton_H__of_isFlasque_of_pos_07aa24bc364e
