-- Prove2me | Theorems.Thm_UlmsTheorem_ulmLength_at_ulmLength
-- name    : UlmsTheorem.ulmLength.at_ulmLength
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:57:07.261693+00:00
-- url     : https://prove2.me/theorems/8af8c0f0-4ffc-4fa9-b877-1a68abefd460
-- title:
--   ulm Length: at ulm Length
-- statement:
--   p^(ulmLength)·G = 0.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/UlmInvariants.lean#L346-L348
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/UlmInvariants.lean#L346-L348

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

theorem UlmsTheorem.ulmLength.at_ulmLength (hred : IsPReduced p G) :
    ulmSubgroup p (ulmLength p (G := G)) (G := G) = ⊥ := by sorry
