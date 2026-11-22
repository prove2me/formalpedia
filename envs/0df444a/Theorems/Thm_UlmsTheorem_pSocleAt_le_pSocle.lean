-- Prove2me | Theorems.Thm_UlmsTheorem_pSocleAt_le_pSocle
-- name    : UlmsTheorem.pSocleAt_le_pSocle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:55:19.332176+00:00
-- url     : https://prove2.me/theorems/8ae8c684-4dd5-4f02-878a-119ce10d30ef
-- title:
--   Ulms Theorem: p Socle At le p Socle
-- statement:
--   The Ulms Theorem construction uses the p Socle At le p Socle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/Socle.lean#L61-L63
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/Socle.lean#L61-L63

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

theorem UlmsTheorem.pSocleAt_le_pSocle (α : Ordinal) :
    pSocleAt p α (G := G) ≤ pSocle p := by sorry
