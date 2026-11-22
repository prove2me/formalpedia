-- Prove2me | Theorems.Thm_UlmsTheorem_relativeUlmInvariant_add_occupiedInvariant
-- name    : UlmsTheorem.relativeUlmInvariant_add_occupiedInvariant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:57:52.40527+00:00
-- url     : https://prove2.me/theorems/af9657b1-d360-4e3b-87b1-a9f400200fb2
-- title:
--   Ulms Theorem: relative Ulm Invariant add occupied Invariant
-- statement:
--   The occupied-space equation underlying the Barwise–Eklof room criterion:
--   `relative room + occupied = the ordinary Ulm invariant`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/UlmInvariants.lean#L277-L284
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/UlmInvariants.lean#L277-L284

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

theorem UlmsTheorem.relativeUlmInvariant_add_occupiedInvariant
    (S : AddSubgroup G) (α : Ordinal) :
    relativeUlmInvariant p S α +
        Module.rank (ZMod p) (relativeOccupiedSubmodule p S α) =
      ulmInvariant p α (G := G) := by sorry
