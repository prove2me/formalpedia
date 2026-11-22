-- Prove2me | Theorems.Thm_UlmsTheorem_not_mem_succ_add_zsmul_of_proper
-- name    : UlmsTheorem.not_mem_succ_add_zsmul_of_proper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:57:42.276165+00:00
-- url     : https://prove2.me/theorems/d1127617-9ab0-48d1-bf61-007380015f97
-- title:
--   Ulms Theorem: not mem succ add zsmul of proper
-- statement:
--   If `x` has exact height `α`, is proper over `A`, and `p • x ∈ A`,
--   then no coefficient prime to `p` can move a translate of `x` into
--   `G_(α+1)`.  This is the filtration form of the height calculation used
--   when Kaplansky says the extended map is still height-preserving.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L992-L1036
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L992-L1036

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

theorem UlmsTheorem.not_mem_succ_add_zsmul_of_proper
    {A : AddSubgroup G} {x : G} {α : Ordinal.{0}}
    (hxα : x ∈ ulmSubgroup p α (G := G))
    (hxSucc : x ∉ ulmSubgroup p (Order.succ α) (G := G))
    (hxProper : IsProper p A x)
    (hpxA : p • x ∈ A)
    (a : A) (n : ℤ) (hn : ¬ (p : ℤ) ∣ n) :
    (a : G) + n • x ∉ ulmSubgroup p (Order.succ α) (G := G) := by sorry
