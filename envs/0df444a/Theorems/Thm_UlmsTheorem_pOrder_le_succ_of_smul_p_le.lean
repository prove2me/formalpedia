-- Prove2me | Theorems.Thm_UlmsTheorem_pOrder_le_succ_of_smul_p_le
-- name    : UlmsTheorem.pOrder_le_succ_of_smul_p_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:54:11.678426+00:00
-- url     : https://prove2.me/theorems/6e0f80b9-85c5-4a34-8cdb-4362a74d9424
-- title:
--   Ulms Theorem: p Order le succ of smul p le
-- statement:
--   Killing `p • x` at level `n` kills `x` at level `n + 1`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Pure.lean#L205-L209
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Pure.lean#L205-L209

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

theorem UlmsTheorem.pOrder_le_succ_of_smul_p_le {x : G} {n : ℕ} (h : pOrder p (p • x) ≤ n) :
    pOrder p x ≤ n + 1 := by sorry
