-- Prove2me | Theorems.Thm_RamanujanNagell_theta_sq
-- name    : RamanujanNagell.theta_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:40:02.500033+00:00
-- url     : https://prove2.me/theorems/0190fbc6-5c0d-46f4-b2da-9e373749ef1a
-- title:
--   Ramanujan Nagell: theta sq
-- statement:
--   The Ramanujan Nagell construction uses the theta sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/RamanujanNagell/Helpers.lean#L46-L46
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/RamanujanNagell/Helpers.lean#L46-L46

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

theorem RamanujanNagell.theta_sq : θ ^ 2 = θ - 2 := by sorry
