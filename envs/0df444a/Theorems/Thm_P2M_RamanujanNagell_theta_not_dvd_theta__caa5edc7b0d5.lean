-- Prove2me | Theorems.Thm_P2M_RamanujanNagell_theta_not_dvd_theta__caa5edc7b0d5
-- name    : P2M_RamanujanNagell_theta_not_dvd_theta__caa5edc7b0d5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:40:19.904279+00:00
-- url     : https://prove2.me/theorems/5af73b71-d31b-4bbd-bed3-83ca9bce8e8c
-- title:
--   P2 M Ramanujan Nagell theta not dvd theta  caa5edc7b0d5: P2 M Ramanujan Nagell theta not dvd theta  caa5edc7b0d5
-- statement:
--   The P2 M Ramanujan Nagell theta not dvd theta  caa5edc7b0d5 construction uses the P2 M Ramanujan Nagell theta not dvd theta  caa5edc7b0d5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/RamanujanNagell/Helpers.lean#L321-L323
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/RamanujanNagell/Helpers.lean#L321-L323

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

theorem P2M_RamanujanNagell_theta_not_dvd_theta__caa5edc7b0d5 : ¬ (θ ∣ θ') := by sorry

alias «RamanujanNagell».«theta_not_dvd_theta'» := P2M_RamanujanNagell_theta_not_dvd_theta__caa5edc7b0d5
