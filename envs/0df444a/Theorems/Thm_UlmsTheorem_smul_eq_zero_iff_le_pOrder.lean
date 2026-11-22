-- Prove2me | Theorems.Thm_UlmsTheorem_smul_eq_zero_iff_le_pOrder
-- name    : UlmsTheorem.smul_eq_zero_iff_le_pOrder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:54:06.627435+00:00
-- url     : https://prove2.me/theorems/6e57f0ad-df2e-4484-9743-388a1648ce69
-- title:
--   Ulms Theorem: smul eq zero iff le p Order
-- statement:
--   The Ulms Theorem construction uses the smul eq zero iff le p Order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Pure.lean#L178-L202
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Pure.lean#L178-L202

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

theorem UlmsTheorem.smul_eq_zero_iff_le_pOrder (x : G) (n : ℕ) :
    p ^ n • x = 0 ↔ pOrder p x ≤ n := by sorry
