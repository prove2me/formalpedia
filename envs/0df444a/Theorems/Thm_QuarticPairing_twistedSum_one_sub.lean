-- Prove2me | Theorems.Thm_QuarticPairing_twistedSum_one_sub
-- name    : QuarticPairing.twistedSum_one_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:34:31.165363+00:00
-- url     : https://prove2.me/theorems/6ec64514-a9d1-5d0e-a88d-adfbf202bcb4
-- title:
--   Quartic Pairing: twisted Sum one sub
-- statement:
--   **The pairing with an exceptional set.** If the identity holds off a set `E`, then
--   `|S_β(X; 1) + κ conj S_β(X; 0)|` is at most twice the weight of `E`.
--
--   Source: https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/QuarticPairing/Pairing.lean#L102-L119
-- source:
--   https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/QuarticPairing/Pairing.lean#L102-L119

module
public import Definitions.Def_QuarticPairing_Defs
public import Definitions.Def_QuarticPairing_Pairing
set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
noncomputable section
open QuarticPairing
open Classical

theorem QuarticPairing.twistedSum_one_sub (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ) (β : GaussianInt)
    {κ : ℂ} (hκ : ‖κ‖ = 1) (E : GaussianInt → Prop)
    (h12 : ∀ c, ¬ E c → Λ c ≠ 0 → g c = 0 ∨ g c ^ 2 = -κ * unitDir c) (X : ℕ) :
    ‖twistedSum g Λ β X 1 + κ * starRingEnd ℂ (twistedSum g Λ β X 0)‖ ≤
      2 * defectSum g Λ β E X := by sorry
