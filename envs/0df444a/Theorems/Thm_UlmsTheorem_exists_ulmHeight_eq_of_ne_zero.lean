-- Prove2me | Theorems.Thm_UlmsTheorem_exists_ulmHeight_eq_of_ne_zero
-- name    : UlmsTheorem.exists_ulmHeight_eq_of_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:54:13.557503+00:00
-- url     : https://prove2.me/theorems/b06263c4-a702-41d8-ae06-9178f908152f
-- title:
--   Ulms Theorem: exists ulm Height eq of ne zero
-- statement:
--   In a reduced `p`-group, every nonzero element has an attained ordinal
--   Ulm height.
--
--   Reducedness supplies a stage missing the element.  The least such stage
--   cannot be zero or a limit stage, so it is a successor `α+1`; minimality then
--   puts the element in `G_α` but not in `G_(α+1)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Pure.lean#L135-L158
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Pure.lean#L135-L158

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

theorem UlmsTheorem.exists_ulmHeight_eq_of_ne_zero
    (hG : IsPReduced p G) {x : G} (hx0 : x ≠ 0) :
    ∃ α : Ordinal.{0},
      x ∈ ulmSubgroup p α (G := G) ∧
      x ∉ ulmSubgroup p (Order.succ α) (G := G) := by sorry
