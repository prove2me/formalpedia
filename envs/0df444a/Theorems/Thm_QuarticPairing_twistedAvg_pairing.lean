-- Prove2me | Theorems.Thm_QuarticPairing_twistedAvg_pairing
-- name    : QuarticPairing.twistedAvg_pairing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:34:47.232822+00:00
-- url     : https://prove2.me/theorems/4ac284ab-0440-5dca-be9d-3b12ad84e1b6
-- title:
--   Quartic Pairing: twisted Avg pairing
-- statement:
--   **The pairing identities** (first form). Let `k ∈ ℤ` (so that `m = 2k + 1` is odd). If on the
--   support of `w` the identity `g(c)² = -κ c/|c|` holds and `conj χ₃(c) = χ(c)`, as for
--   `χ = (ν/c)₄` and `χ₃ = (ν³/c)₄`, then
--   `∑ conj(χ₃(c)) g(c) (c/|c|)^{-k-1} w(c) = -κ conj (∑ conj(χ(c)) g(c) (c/|c|)^k w(c))`,
--   that is `A(ν³, -m) = -κ conj A(ν, m)`.
--
--   Source: https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/QuarticPairing/Pairing.lean#L169-L196
-- source:
--   https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/QuarticPairing/Pairing.lean#L169-L196

module
public import Definitions.Def_QuarticPairing_Defs
public import Definitions.Def_QuarticPairing_Pairing
set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
noncomputable section
open QuarticPairing

theorem QuarticPairing.twistedAvg_pairing (χ χ₃ g : GaussianInt → ℂ) (w : GaussianInt → ℝ)
    (s : Finset GaussianInt) {κ : ℂ} (hκ : ‖κ‖ = 1)
    (hχ : ∀ c ∈ s, w c ≠ 0 → starRingEnd ℂ (χ₃ c) = χ c)
    (h12 : ∀ c ∈ s, w c ≠ 0 → g c = 0 ∨ g c ^ 2 = -κ * unitDir c) (k : ℤ) :
    twistedAvg χ₃ g w s (-k - 1) = -κ * starRingEnd ℂ (twistedAvg χ g w s k) := by sorry
