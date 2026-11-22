-- Prove2me | Theorems.Thm_UlmsTheorem_ulmLength_exists_zero
-- name    : UlmsTheorem.ulmLength.exists_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:57:04.19459+00:00
-- url     : https://prove2.me/theorems/2d37b851-28a3-4957-ac2c-4197ea2440a5
-- title:
--   ulm Length: exists zero
-- statement:
--   The set `{α | p^α·G = 0}` is nonempty for a reduced p-group.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/UlmInvariants.lean#L340-L342
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/UlmInvariants.lean#L340-L342

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
omit hp

theorem UlmsTheorem.ulmLength.exists_zero (hred' : IsPReduced p G) :
    ∃ α : Ordinal.{0}, ulmSubgroup p α (G := G) = ⊥ := by sorry
