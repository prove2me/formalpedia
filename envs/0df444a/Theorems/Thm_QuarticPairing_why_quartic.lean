-- Prove2me | Theorems.Thm_QuarticPairing_why_quartic
-- name    : QuarticPairing.why_quartic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:39:23.100444+00:00
-- url     : https://prove2.me/theorems/d7cb4429-1f28-4323-8e11-2e7217b8b1c2
-- title:
--   Quartic Pairing: why quartic
-- statement:
--   **Why quartic.** If `|g| = 1` and `g^k = ξ` with `k ≥ 1`, then `ḡ = g^{k-1} ξ̄`.
--
--   Source: https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/Solution.lean#L55-L57
-- source:
--   https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/Solution.lean#L55-L57

module
public import Definitions.Def_QuarticPairing
public import Definitions.Def_QuarticPairing_Solution
set_option autoImplicit true
@[expose] public section
public section
open Complex Finset Asymptotics
noncomputable section
open QuarticPairing

theorem QuarticPairing.why_quartic {g ξ : ℂ} {k : ℕ} (hk : 1 ≤ k) (hg : ‖g‖ = 1) (h : g ^ k = ξ) :
    starRingEnd ℂ g = g ^ (k - 1) * starRingEnd ℂ ξ := by sorry
