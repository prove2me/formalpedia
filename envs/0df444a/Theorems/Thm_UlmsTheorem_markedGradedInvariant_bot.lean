-- Prove2me | Theorems.Thm_UlmsTheorem_markedGradedInvariant_bot
-- name    : UlmsTheorem.markedGradedInvariant_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:57:15.898909+00:00
-- url     : https://prove2.me/theorems/7a3adcac-abb4-4524-890c-92fe8e43778c
-- title:
--   Ulms Theorem: marked Graded Invariant bot
-- statement:
--   With no marked subgroup, the marked-graded invariant is the ordinary Ulm invariant.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/UlmInvariants.lean#L158-L170
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/UlmInvariants.lean#L158-L170

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

theorem UlmsTheorem.markedGradedInvariant_bot (α : Ordinal) :
    markedGradedInvariant p (⊥ : AddSubgroup G) α = ulmInvariant p α (G := G) := by sorry
