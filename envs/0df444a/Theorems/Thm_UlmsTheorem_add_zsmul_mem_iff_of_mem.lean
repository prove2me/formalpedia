-- Prove2me | Theorems.Thm_UlmsTheorem_add_zsmul_mem_iff_of_mem
-- name    : UlmsTheorem.add_zsmul_mem_iff_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:53:38.2325+00:00
-- url     : https://prove2.me/theorems/35055620-9fef-4939-8068-e690f4abad38
-- title:
--   Ulms Theorem: add zsmul mem iff of mem
-- statement:
--   Translating by a multiple of an element already in `G_β` does not change
--   membership in `G_β`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/UlmSubgroups.lean#L163-L172
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/UlmSubgroups.lean#L163-L172

module
public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Mathlib.Algebra.Group.Subgroup.Map
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Subgroups
public import Mathlib.Algebra.Module.NatInt
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmSubgroups
set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
open Ordinal
variable (p : ℕ)
variable {G : Type*} [AddCommGroup G]

theorem UlmsTheorem.add_zsmul_mem_iff_of_mem {β : Ordinal.{0}} {x c : G}
    (hx : x ∈ ulmSubgroup p β (G := G)) (n : ℤ) :
    c + n • x ∈ ulmSubgroup p β (G := G) ↔ c ∈ ulmSubgroup p β (G := G) := by sorry
