-- Prove2me | Theorems.Thm_UlmsTheorem_pSocleAt_zero
-- name    : UlmsTheorem.pSocleAt_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:55:17.861189+00:00
-- url     : https://prove2.me/theorems/912eaac9-32ba-47d9-a7c5-04c09d934a48
-- title:
--   Ulms Theorem: p Socle At zero
-- statement:
--   The Ulms Theorem construction uses the p Socle At zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/Socle.lean#L51-L52
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/Socle.lean#L51-L52

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

theorem UlmsTheorem.pSocleAt_zero : pSocleAt p (0 : Ordinal) (G := G) = pSocle p := by sorry
