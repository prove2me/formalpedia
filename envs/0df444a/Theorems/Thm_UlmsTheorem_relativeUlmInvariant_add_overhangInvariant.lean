-- Prove2me | Theorems.Thm_UlmsTheorem_relativeUlmInvariant_add_overhangInvariant
-- name    : UlmsTheorem.relativeUlmInvariant_add_overhangInvariant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:58:01.448572+00:00
-- url     : https://prove2.me/theorems/ee3c7661-aef3-4b09-b1da-5182798576ed
-- title:
--   Ulms Theorem: relative Ulm Invariant add overhang Invariant
-- statement:
--   The same BCM equation in relative-Ulm terminology.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/UlmInvariants.lean#L319-L323
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/UlmInvariants.lean#L319-L323

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

theorem UlmsTheorem.relativeUlmInvariant_add_overhangInvariant
    (S : AddSubgroup G) (α : Ordinal) :
    relativeUlmInvariant p S α + overhangInvariant (p := p) S α =
      markedGradedInvariant p S α := by sorry
