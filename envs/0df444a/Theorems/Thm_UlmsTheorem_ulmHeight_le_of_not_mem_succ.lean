-- Prove2me | Theorems.Thm_UlmsTheorem_ulmHeight_le_of_not_mem_succ
-- name    : UlmsTheorem.ulmHeight_le_of_not_mem_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:54:09.77553+00:00
-- url     : https://prove2.me/theorems/482ecd71-cc1b-4a9d-a64d-5faf538b1416
-- title:
--   Ulms Theorem: ulm Height le of not mem succ
-- statement:
--   Failure of membership at the successor of `α` bounds the Ulm height by `α`.
--
--   Unlike the exact-height lemma below, this does not assume membership in `G_α`.
--   It is useful when properness rules out a higher representative in a coset.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Pure.lean#L60-L65
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Pure.lean#L60-L65

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

theorem UlmsTheorem.ulmHeight_le_of_not_mem_succ (x : G) (α : Ordinal.{0})
    (hxs : x ∉ ulmSubgroup p (Order.succ α) (G := G)) :
    ulmHeight p x ≤ (α : WithTop Ordinal.{0}) := by sorry
