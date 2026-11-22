-- Prove2me | Theorems.Thm_UlmsTheorem_pOrder_smul_p
-- name    : UlmsTheorem.pOrder_smul_p
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:54:16.373665+00:00
-- url     : https://prove2.me/theorems/04a83e93-1373-49ec-bf6e-7789c646645b
-- title:
--   Ulms Theorem: p Order smul p
-- statement:
--   The Ulms Theorem construction uses the p Order smul p property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Pure.lean#L218-L250
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Pure.lean#L218-L250

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

theorem UlmsTheorem.pOrder_smul_p (x : G) (hx : 0 < pOrder p x) :
    pOrder p (p • x) = pOrder p x - 1 := by sorry
