-- Prove2me | Theorems.Thm_SCCThm8_Rig_exists_kset
-- name    : SCCThm8.Rig.exists_kset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:47:38.826317+00:00
-- url     : https://prove2.me/theorems/ae581a25-af1b-423f-88af-25a748f70d2d
-- title:
--   Rig: exists kset
-- statement:
--   The Rig construction uses the exists kset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Rigidity.lean#L31-L36
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Rigidity.lean#L31-L36

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Rigidity
set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset
open SCCThm8.Rig
variable {n : ℕ}

theorem SCCThm8.Rig.exists_kset {k : ℕ} (s t : Finset (Fin n)) (hst : Disjoint s t) (hs : s.card ≤ k)
    (ht : k + t.card ≤ n) : ∃ A : Finset (Fin n), A.card = k ∧ s ⊆ A ∧ Disjoint A t := by sorry
