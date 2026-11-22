-- Prove2me | Theorems.Thm_UlmsTheorem_ulmLength_inv_zero_of_ge
-- name    : UlmsTheorem.ulmLength.inv_zero_of_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:58:11.343261+00:00
-- url     : https://prove2.me/theorems/b701b334-dbe4-4613-83ae-ccc793e7ee5c
-- title:
--   ulm Length: inv zero of ge
-- statement:
--   Ulm invariants vanish above the Ulm length.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/UlmInvariants.lean#L351-L373
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/UlmInvariants.lean#L351-L373

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
open UlmsTheorem.ulmLength
variable {G : Type*} [AddCommGroup G]

theorem UlmsTheorem.ulmLength.inv_zero_of_ge (hred : IsPReduced p G)
    (α : Ordinal) (hα : ulmLength p (G := G) ≤ α) :
    ulmInvariant p α (G := G) = 0 := by sorry
