-- Prove2me | Theorems.Thm_UlmsTheorem_mem_ulmSubgroup_of_le_ulmHeight
-- name    : UlmsTheorem.mem_ulmSubgroup_of_le_ulmHeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:54:13.171685+00:00
-- url     : https://prove2.me/theorems/53aad41f-ba87-4e4c-83ce-2acb2e4ea251
-- title:
--   Ulms Theorem: mem ulm Subgroup of le ulm Height
-- statement:
--   **The converse of `coe_le_ulmHeight_of_mem`.**  A lower bound on the Ulm
--   height is membership in the filtration: if `γ ≤ h(x)` then `x ∈ G_γ`.
--
--   The supremum defining `ulmHeight` is therefore attained whenever it is bounded by
--   an ordinal, so `h(x) ≥ γ` and `x ∈ G_γ` are interchangeable.  This is the bridge
--   that lets a height condition stated with `ulmHeight` be used as a filtration
--   hypothesis.
--
--   The three cases are genuinely different: at `0` the filtration is everything, at a
--   successor the previous lemma bounds the height strictly below, and at a limit the
--   inductive hypothesis supplies membership at every smaller level, which is exactly
--   the intersection defining `G_γ`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Pure.lean#L79-L95
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Pure.lean#L79-L95

module
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Heights
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Tactic.NormNum.GCD
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Pure
set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
open Ordinal
universe u
variable (p : ℕ)
variable {G : Type u} [AddCommGroup G]
variable {H : Type u} [AddCommGroup H]

theorem UlmsTheorem.mem_ulmSubgroup_of_le_ulmHeight (x : G) (γ : Ordinal.{0})
    (h : (γ : WithTop Ordinal.{0}) ≤ ulmHeight p x) :
    x ∈ ulmSubgroup p γ (G := G) := by sorry
