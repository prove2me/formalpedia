-- Prove2me | Theorems.Thm_UlmsTheorem_hillInvariant_bot
-- name    : UlmsTheorem.hillInvariant_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:57:15.918+00:00
-- url     : https://prove2.me/theorems/cb5bca40-a9bc-4d44-91af-857021d89e77
-- title:
--   Ulms Theorem: hill Invariant bot
-- statement:
--   With no marked subgroup, the Hill invariant is the ordinary Ulm invariant.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/UlmInvariants.lean#L195-L216
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/UlmInvariants.lean#L195-L216

module
public import Mathlib.Algebra.Field.ZMod
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Socle
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Heights
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmInvariants
set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
open Ordinal Cardinal
variable (p : ℕ) [hp : Fact p.Prime]
variable {G : Type*} [AddCommGroup G]

theorem UlmsTheorem.hillInvariant_bot (α : Ordinal) :
    hillInvariant p (⊥ : AddSubgroup G) α = ulmInvariant p α (G := G) := by sorry
