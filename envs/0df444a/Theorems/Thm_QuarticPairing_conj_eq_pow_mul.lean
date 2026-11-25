-- Prove2me | Theorems.Thm_QuarticPairing_conj_eq_pow_mul
-- name    : QuarticPairing.conj_eq_pow_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:34:51.467626+00:00
-- url     : https://prove2.me/theorems/5091bdec-28f6-5730-90d7-dc17d331ba33
-- title:
--   Quartic Pairing: conj eq pow mul
-- statement:
--   **Why quartic.** If `|g| = 1` and `g^k = ξ` with `k ≥ 1`, then `ḡ = g^{k-1} ξ̄`. For the quartic
--   Gauss sum `k = 2`, so conjugation carries a twisted first moment to a twisted first moment; for
--   `k ≥ 3` it lands on the `(k-1)`-st moment.
--
--   Source: https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/QuarticPairing/Pairing.lean#L201-L207
-- source:
--   https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/QuarticPairing/Pairing.lean#L201-L207

module
public import Definitions.Def_QuarticPairing_Defs
public import Definitions.Def_QuarticPairing_Pairing
set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
noncomputable section
open QuarticPairing

theorem QuarticPairing.conj_eq_pow_mul {g ξ : ℂ} {k : ℕ} (hk : 1 ≤ k) (hg : ‖g‖ = 1) (h : g ^ k = ξ) :
    starRingEnd ℂ g = g ^ (k - 1) * starRingEnd ℂ ξ := by sorry
