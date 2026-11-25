-- Prove2me | Theorems.Thm_QuarticPairing_amendedMain_reflect
-- name    : QuarticPairing.amendedMain_reflect
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:36:46.663558+00:00
-- url     : https://prove2.me/theorems/ca134307-1478-4145-8640-2de39c909fdb
-- title:
--   Quartic Pairing: amended Main reflect
-- statement:
--   The main terms of the amended conjecture satisfy `M(1 - ℓ) = -κ conj M(ℓ)`.
--
--   Source: https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/QuarticPairing/Amended.lean#L34-L49
-- source:
--   https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/QuarticPairing/Amended.lean#L34-L49

module
public import Definitions.Def_QuarticPairing_Inconsistency
public import Definitions.Def_QuarticPairing_Amended
set_option autoImplicit true
@[expose] public section
public section
open Complex Filter Asymptotics Finset
noncomputable section
open QuarticPairing

theorem QuarticPairing.amendedMain_reflect {κ : ℂ} (hκ : ‖κ‖ = 1) (b : ℂ) (X : ℕ) (ℓ : ℤ) :
    amendedMain κ b X (1 - ℓ) = -κ * starRingEnd ℂ (amendedMain κ b X ℓ) := by sorry
