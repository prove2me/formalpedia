-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_insertCollisionAux_mem
-- name    : VerifiedHAMT.SetWithoutValArray.Raw.insertCollisionAux_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:43:39.334694+00:00
-- url     : https://prove2.me/theorems/ca35f8a5-8728-4d4c-98af-97f57addee37
-- title:
--   Raw: insert Collision Aux mem
-- statement:
--   The Raw construction uses the insert Collision Aux mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/InsertProofs.lean#L14-L27
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/InsertProofs.lean#L14-L27

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Insert
public import Definitions.Def_VerifiedHAMT_Util
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertProofs
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
open Lean.PersistentHashMap (shift maxDepth)
variable {α : Type u}

theorem VerifiedHAMT.SetWithoutValArray.Raw.insertCollisionAux_mem [BEq α] [LawfulBEq α]
    (keys : Array α)
    (i : Nat) (key q : α) :
    HasKey q (insertCollisionAux ⟨.collision keys, .mk ..⟩ i key).val ↔
      q = key ∨ HasKey q (.collision keys) := by sorry
