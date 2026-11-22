-- Prove2me | Theorems.Thm_Rollback_isRollback_iff_maximal
-- name    : Rollback.isRollback_iff_maximal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:01:57.0688+00:00
-- url     : https://prove2.me/theorems/8276379a-4adf-4efb-8fc7-e4a316904462
-- title:
--   Rollback: is Rollback iff maximal
-- statement:
--   The Rollback construction uses the is Rollback iff maximal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Rollback.lean#L42-L57
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Rollback.lean#L42-L57

import Definitions.Def_EventStructures_Family_Basic
import Definitions.Def_EventStructures_Family_Reachability
import Definitions.Def_EventStructures_Family_Rollback
set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L)
open Rollback

theorem Rollback.isRollback_iff_maximal {c : Conf F} {e : F.Event} {m : Conf F} :
    isRollback F c e m ↔ m ∈ RollbackCandidates F c e ∧
      ∀ m' : Conf F, m' ∈ RollbackCandidates F c e → m.1 ⊆ m'.1 → m'.1 ⊆ m.1 := by sorry
