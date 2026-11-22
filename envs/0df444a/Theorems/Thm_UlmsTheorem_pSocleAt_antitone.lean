-- Prove2me | Theorems.Thm_UlmsTheorem_pSocleAt_antitone
-- name    : UlmsTheorem.pSocleAt_antitone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:55:15.644076+00:00
-- url     : https://prove2.me/theorems/d0e2fe39-2a87-4393-a97e-bd26c9578080
-- title:
--   Ulms Theorem: p Socle At antitone
-- statement:
--   The Ulms Theorem construction uses the p Socle At antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/Socle.lean#L54-L55
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/Socle.lean#L54-L55

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

theorem UlmsTheorem.pSocleAt_antitone : Antitone (fun α ↦ pSocleAt p α (G := G)) := by sorry
