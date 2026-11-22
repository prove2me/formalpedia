-- Prove2me | Theorems.Thm_UlmsTheorem_ulmHeight_zsmul
-- name    : UlmsTheorem.ulmHeight_zsmul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:54:23.809041+00:00
-- url     : https://prove2.me/theorems/3b883325-250d-456f-9e71-67b9e0fa2724
-- title:
--   Ulms Theorem: ulm Height zsmul
-- statement:
--   Multiplication by an integer prime to `p` preserves Ulm height.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Pure.lean#L367-L374
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Pure.lean#L367-L374

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

theorem UlmsTheorem.ulmHeight_zsmul [Fact p.Prime] (hprim : IsPrimaryPGroup p G)
    {n : ℤ} (hn : ¬ (p : ℤ) ∣ n) (u : G) :
    ulmHeight p (n • u) = ulmHeight p u := by sorry
