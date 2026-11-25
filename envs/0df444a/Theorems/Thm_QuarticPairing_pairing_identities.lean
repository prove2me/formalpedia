-- Prove2me | Theorems.Thm_QuarticPairing_pairing_identities
-- name    : QuarticPairing.pairing_identities
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:38:34.069664+00:00
-- url     : https://prove2.me/theorems/5b80d38f-1289-4e7b-93c3-9622b70be889
-- title:
--   Quartic Pairing: pairing identities
-- statement:
--   **The pairing identities.** For `k ∈ ℤ` (`m = 2k + 1`), if on the support of `w`
--   `g(c)² = -κ c/|c|` and `conj χ₃(c) = χ(c)` (as for `χ = (ν/c)₄`, `χ₃ = (ν³/c)₄`), then
--   `A(ν³, -m) = -κ conj A(ν, m)`.
--
--   Source: https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/Solution.lean#L47-L52
-- source:
--   https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/Solution.lean#L47-L52

module
public import Definitions.Def_QuarticPairing
public import Definitions.Def_QuarticPairing_Solution
set_option autoImplicit true
@[expose] public section
public section
open Complex Finset Asymptotics
noncomputable section
open QuarticPairing

theorem QuarticPairing.pairing_identities (χ χ₃ g : GaussianInt → ℂ) (w : GaussianInt → ℝ)
    (s : Finset GaussianInt) {κ : ℂ} (hκ : ‖κ‖ = 1)
    (hχ : ∀ c ∈ s, w c ≠ 0 → starRingEnd ℂ (χ₃ c) = χ c)
    (h12 : ∀ c ∈ s, w c ≠ 0 → g c = 0 ∨ g c ^ 2 = -κ * unitDir c) (k : ℤ) :
    twistedAvg χ₃ g w s (-k - 1) = -κ * starRingEnd ℂ (twistedAvg χ g w s k) := by sorry
