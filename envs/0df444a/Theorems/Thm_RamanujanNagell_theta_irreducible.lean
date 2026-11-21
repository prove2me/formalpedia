-- Prove2me | Theorems.Thm_RamanujanNagell_theta_irreducible
-- name    : RamanujanNagell.theta_irreducible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:40:06.540063+00:00
-- url     : https://prove2.me/theorems/fdcfb2b8-a006-49e9-a4a0-cf9121c326d6
-- title:
--   Ramanujan Nagell: theta irreducible
-- statement:
--   The Ramanujan Nagell construction uses the theta irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/RamanujanNagell/Helpers.lean#L139-L139
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/RamanujanNagell/Helpers.lean#L139-L139

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

theorem RamanujanNagell.theta_irreducible : Irreducible θ := by sorry
