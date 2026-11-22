-- Prove2me | Theorems.Thm_UlmsTheorem_pOrder_zero
-- name    : UlmsTheorem.pOrder_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:54:04.72427+00:00
-- url     : https://prove2.me/theorems/4462bdb0-5db6-40c0-b8f3-df74bf8af589
-- title:
--   Ulms Theorem: p Order zero
-- statement:
--   The Ulms Theorem construction uses the p Order zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Pure.lean#L175-L176
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Pure.lean#L175-L176

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

theorem UlmsTheorem.pOrder_zero : pOrder p (0 : G) = 0 := by sorry
