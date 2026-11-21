-- Prove2me | Theorems.Thm_RamanujanNagell_two_factorisation_R
-- name    : RamanujanNagell.two_factorisation_R
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:40:05.456178+00:00
-- url     : https://prove2.me/theorems/78cb7432-f10c-4191-b1ce-3984ef1d4a91
-- title:
--   Ramanujan Nagell: two factorisation R
-- statement:
--   For backward compatibility with the old Helpers API.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/RamanujanNagell/Helpers.lean#L55-L55
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/RamanujanNagell/Helpers.lean#L55-L55

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

theorem RamanujanNagell.two_factorisation_R : θ * (1 - θ) = 2 := by sorry
