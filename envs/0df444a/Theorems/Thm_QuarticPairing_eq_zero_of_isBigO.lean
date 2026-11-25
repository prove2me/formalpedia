-- Prove2me | Theorems.Thm_QuarticPairing_eq_zero_of_isBigO
-- name    : QuarticPairing.eq_zero_of_isBigO
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:35:07.70093+00:00
-- url     : https://prove2.me/theorems/02e91729-ee73-5b2e-94b0-6d35c281eb2c
-- title:
--   Quartic Pairing: eq zero of is Big O
-- statement:
--   A term `b X^{3/4}` that is `O(X^{5/8})` along the integers has `b = 0`.
--
--   Source: https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/QuarticPairing/Inconsistency.lean#L27-L47
-- source:
--   https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/QuarticPairing/Inconsistency.lean#L27-L47

module
public import Definitions.Def_QuarticPairing_Pairing
public import Definitions.Def_QuarticPairing_Inconsistency
set_option autoImplicit true
@[expose] public section
public section
open Complex Filter Asymptotics Finset
noncomputable section
open QuarticPairing

theorem QuarticPairing.eq_zero_of_isBigO {b : ℂ}
    (h : (fun X : ℕ => b * ((((X : ℝ) ^ ((3 : ℝ) / 4) : ℝ)) : ℂ)) =O[atTop]
      (fun X : ℕ => (X : ℝ) ^ ((5 : ℝ) / 8))) : b = 0 := by sorry
