-- Prove2me | Theorems.Thm_UlmsTheorem_pSocleAt_succ_le
-- name    : UlmsTheorem.pSocleAt_succ_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:55:23.373535+00:00
-- url     : https://prove2.me/theorems/c964fe9a-08d9-467f-8b40-166b8cd5a7f8
-- title:
--   Ulms Theorem: p Socle At succ le
-- statement:
--   The Ulms Theorem construction uses the p Socle At succ le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/Socle.lean#L57-L59
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/Socle.lean#L57-L59

module
public import Mathlib.Algebra.Module.ZMod
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmSubgroups
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Socle
set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
open Ordinal
variable (p : ℕ)
variable {G : Type*} [AddCommGroup G]

theorem UlmsTheorem.pSocleAt_succ_le (α : Ordinal) :
    pSocleAt p (Order.succ α) (G := G) ≤ pSocleAt p α := by sorry
