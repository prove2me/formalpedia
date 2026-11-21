-- Prove2me | Theorems.Thm_RamanujanNagell_norm_eq
-- name    : RamanujanNagell.norm_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:40:03.775937+00:00
-- url     : https://prove2.me/theorems/6fd36023-ab5e-44cd-a3d3-366da024c235
-- title:
--   Ramanujan Nagell: norm eq
-- statement:
--   The Ramanujan Nagell construction uses the norm eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/RamanujanNagell/Helpers.lean#L61-L62
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/RamanujanNagell/Helpers.lean#L61-L62

module
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum.GCD
public import Definitions.Def_LeanPool_RamanujanNagell_Helpers
set_option autoImplicit true
@[expose] public section
public section
open RamanujanNagell
open QuadraticAlgebra

theorem RamanujanNagell.norm_eq (x y : ℤ) : QuadraticAlgebra.norm (⟨x, y⟩ : R) = x ^ 2 + x * y + 2 * y ^ 2 := by sorry
