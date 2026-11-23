-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_insertCollisionAux_unique
-- name    : VerifiedHAMT.SetWithoutValArray.Raw.insertCollisionAux_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:43:46.455934+00:00
-- url     : https://prove2.me/theorems/18d8d1dc-285d-4d23-a10f-ad53815ffbf6
-- title:
--   Raw: insert Collision Aux unique
-- statement:
--   The Raw construction uses the insert Collision Aux unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Unique.lean#L16-L31
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Unique.lean#L16-L31

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertProofs
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Size
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Unique
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
open Lean.PersistentHashMap (shift maxDepth)
variable {α : Type u}

theorem VerifiedHAMT.SetWithoutValArray.Raw.insertCollisionAux_unique [BEq α] [LawfulBEq α] (keys : Array α)
    (hu : DistinctKeys keys) (i : Nat) (key : α)
    (scanned : ∀ (j : Nat) (hj : j < keys.size), j < i → keys[j] ≠ key) :
    Unique (insertCollisionAux ⟨.collision keys, .mk ..⟩ i key).val := by sorry
