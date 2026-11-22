-- Prove2me | Theorems.Thm_UlmsTheorem_hillInvariant_add_overhangInvariant
-- name    : UlmsTheorem.hillInvariant_add_overhangInvariant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:56:06.725179+00:00
-- url     : https://prove2.me/theorems/ab80f6d2-9be7-4931-bf5a-740e5c9a0f96
-- title:
--   Ulms Theorem: hill Invariant add overhang Invariant
-- statement:
--   BCM's exact-sequence dimension equation:
--   the marked-graded invariant is the Hill invariant plus the overhang dimension.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/UlmInvariants.lean#L307-L316
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/UlmInvariants.lean#L307-L316

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

theorem UlmsTheorem.hillInvariant_add_overhangInvariant
    (S : AddSubgroup G) (α : Ordinal) :
    hillInvariant p S α + overhangInvariant (p := p) S α =
      markedGradedInvariant p S α := by sorry
