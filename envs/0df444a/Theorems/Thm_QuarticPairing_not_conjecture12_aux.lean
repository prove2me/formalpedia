-- Prove2me | Theorems.Thm_QuarticPairing_not_conjecture12_aux
-- name    : QuarticPairing.not_conjecture12_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:34:58.695424+00:00
-- url     : https://prove2.me/theorems/140548c6-2cf7-573f-9843-bf27b7bba6bb
-- title:
--   Quartic Pairing: not conjecture12 aux
-- statement:
--   The conclusion from the cases `ℓ = 0` and `ℓ = 1`, given that `S_β(X; 0)` is `O(X^{5/8})`.
--
--   Source: https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/QuarticPairing/Inconsistency.lean#L50-L61
-- source:
--   https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/QuarticPairing/Inconsistency.lean#L50-L61

module
public import Definitions.Def_QuarticPairing_Pairing
public import Definitions.Def_QuarticPairing_Inconsistency
set_option autoImplicit true
@[expose] public section
public section
open Complex Filter Asymptotics Finset
noncomputable section
open QuarticPairing

theorem QuarticPairing.not_conjecture12_aux (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ) (β : GaussianInt)
    (hS : (fun X : ℕ => ‖twistedSum g Λ β X 1‖) =O[atTop] (fun X : ℕ => (X : ℝ) ^ ((5 : ℝ) / 8)) →
      (fun X : ℕ => twistedSum g Λ β X 0) =O[atTop] (fun X : ℕ => (X : ℝ) ^ ((5 : ℝ) / 8))) :
    ¬ Conjecture12 g Λ β := by sorry
