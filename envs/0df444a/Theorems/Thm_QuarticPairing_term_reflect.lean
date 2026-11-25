-- Prove2me | Theorems.Thm_QuarticPairing_term_reflect
-- name    : QuarticPairing.term_reflect
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:34:28.2742+00:00
-- url     : https://prove2.me/theorems/de3966c7-55de-4e7c-845e-3157d3d7e481
-- title:
--   Quartic Pairing: term reflect
-- statement:
--   The summand identity behind `twistedSum_reflect`.
--
--   Source: https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/QuarticPairing/Pairing.lean#L126-L152
-- source:
--   https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/QuarticPairing/Pairing.lean#L126-L152

module
public import Definitions.Def_QuarticPairing_Defs
public import Definitions.Def_QuarticPairing_Pairing
set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
noncomputable section
open QuarticPairing

theorem QuarticPairing.term_reflect (g κ : ℂ) (hκ : ‖κ‖ = 1) (c : GaussianInt) (Λ : ℝ)
    (h : Λ ≠ 0 → g = 0 ∨ g ^ 2 = -κ * unitDir c) (ℓ : ℤ) :
    g * starRingEnd ℂ (unitDir c) ^ (1 - ℓ) * (Λ : ℂ) =
      -κ * starRingEnd ℂ (g * starRingEnd ℂ (unitDir c) ^ ℓ * (Λ : ℂ)) := by sorry
