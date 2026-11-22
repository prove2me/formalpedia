-- Prove2me | Theorems.Thm_TaylorVanishingDecay
-- name    : TaylorVanishingDecay
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:13:38.641847+00:00
-- url     : https://prove2.me/theorems/87f494e0-8294-4693-867d-1d48a2c2228a
-- title:
--   Taylor Vanishing Decay: Taylor Vanishing Decay
-- statement:
--   High-order decay from diagonal vanishing plus a Holder bound on the top
--   derivative.  If `u` is `C^k` on `ball x₀ ρ`, every diagonal evaluation
--   `iteratedFDeriv ℝ j u x₀ (fun _ => w)` vanishes for `j ≤ k`, and `iteratedFDeriv ℝ k u`
--   is `β`-Holder with constant `C` on that ball, then
--   `|u x| ≤ (C / k!) * ‖x - x₀‖ ^ (k + β)` there.
--
--   The exponent `k + β` is strictly larger than `k`, which is exactly what the paper's
--   decay estimate at a critical point needs and what degree-`k` vanishing alone cannot
--   give.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/TaylorVanishingDecay.lean#L12-L148
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/TaylorVanishingDecay.lean#L12-L148

import Definitions.Def_PHigherOrder_IteratedDerivAlongRay
import Definitions.Def_PHigherOrder_TaylorVanishingDecay
import Theorems.Thm_IteratedDerivAlongRay

set_option autoImplicit false

theorem TaylorVanishingDecay (u : Plane → ℝ) (x₀ : Plane) (ρ : ℝ) (hρ : 0 < ρ)
    (k : ℕ) (hk : 1 ≤ k) (β : ℝ) (hβ : 0 < β) (C : ℝ) (hC : 0 ≤ C)
    (hu : ContDiffOn ℝ (k : ℕ∞) u (Metric.ball x₀ ρ))
    (hvanish : ∀ j ≤ k, ∀ w : Plane, iteratedFDeriv ℝ j u x₀ (fun _ => w) = 0)
    (hhold : ∀ x ∈ Metric.ball x₀ ρ, ∀ y ∈ Metric.ball x₀ ρ,
        ‖iteratedFDeriv ℝ k u x - iteratedFDeriv ℝ k u y‖ ≤ C * ‖x - y‖ ^ β) :
    ∀ x ∈ Metric.ball x₀ ρ,
      |u x| ≤ C / (Nat.factorial k : ℝ) * ‖x - x₀‖ ^ ((k : ℝ) + β) := by sorry
