-- Prove2me | Theorems.Thm_UlmsTheorem_ulmQuotient_orderOf_dvd_p
-- name    : UlmsTheorem.ulmQuotient_orderOf_dvd_p
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:57:16.861323+00:00
-- url     : https://prove2.me/theorems/b2e4707b-b5fc-41ce-8992-6c0a1bbd18dd
-- title:
--   Ulms Theorem: ulm Quotient order Of dvd p
-- statement:
--   Every element of the classical Ulm quotient has order `p`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/UlmInvariants.lean#L113-L122
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/UlmInvariants.lean#L113-L122

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

theorem UlmsTheorem.ulmQuotient_orderOf_dvd_p {G : Type*} [AddCommGroup G] (α : Ordinal)
    (x : ulmQuotient p α (G := G)) : p • x = 0 := by sorry
