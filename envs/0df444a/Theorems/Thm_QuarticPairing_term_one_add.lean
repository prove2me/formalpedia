-- Prove2me | Theorems.Thm_QuarticPairing_term_one_add
-- name    : QuarticPairing.term_one_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:33:58.531722+00:00
-- url     : https://prove2.me/theorems/cf5cacd1-f39d-5eb5-80ea-a2657cc48612
-- title:
--   Quartic Pairing: term one add
-- statement:
--   The summand identity behind `twistedSum_one`.
--
--   Source: https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/QuarticPairing/Pairing.lean#L79-L86
-- source:
--   https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/QuarticPairing/Pairing.lean#L79-L86

module
public import Definitions.Def_QuarticPairing_Defs
public import Definitions.Def_QuarticPairing_Pairing
set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
noncomputable section
open QuarticPairing

theorem QuarticPairing.term_one_add (g κ : ℂ) (hκ : ‖κ‖ = 1) (c : GaussianInt) (Λ : ℝ)
    (h : Λ ≠ 0 → g = 0 ∨ g ^ 2 = -κ * unitDir c) :
    g * starRingEnd ℂ (unitDir c) ^ (1 : ℤ) * (Λ : ℂ) +
      κ * starRingEnd ℂ (g * starRingEnd ℂ (unitDir c) ^ (0 : ℤ) * (Λ : ℂ)) = 0 := by sorry
