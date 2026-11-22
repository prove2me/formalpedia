-- Prove2me | Theorems.Thm_UlmsTheorem_kaplanskyDomain_rank_eq
-- name    : UlmsTheorem.kaplanskyDomain_rank_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:57:26.23065+00:00
-- url     : https://prove2.me/theorems/51fba967-e44a-495b-8181-959282f1fe40
-- title:
--   Ulms Theorem: kaplansky Domain rank eq
-- statement:
--   Corresponding finite stages give Kaplansky source quotients of equal
--   `ZMod p`-dimension.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L629-L642
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L629-L642

module
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmInvariants
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Pure
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Extension
set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
open Ordinal
universe u
variable (p : ℕ) [hp : Fact p.Prime]
variable {G : Type u} [AddCommGroup G]
variable {H : Type u} [AddCommGroup H]

theorem UlmsTheorem.kaplanskyDomain_rank_eq
    {α : Ordinal.{0}} (s : UlmStageAt p (G := G) (H := H) α) :
    Module.rank (ZMod p) (kaplanskyDomainQuotient p s.A α) =
      Module.rank (ZMod p) (kaplanskyDomainQuotient p s.B α) := by sorry
