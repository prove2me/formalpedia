-- Prove2me | Theorems.Thm_SoficGroups_bad_cut_card_bound
-- name    : SoficGroups.bad_cut_card_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:18.478977+00:00
-- url     : https://prove2.me/theorems/aa6bc0e6-5473-4156-b0c4-e3fb024a4c18
-- title:
--   SoficGroups.bad_cut_card_bound
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff

theorem SoficGroups.bad_cut_card_bound {γ ell a : ℝ} {N b q : ℕ}
    (hgap : ell < γ)
    (hadd : γ * (b : ℝ) - a * (N : ℝ) ≤ (q : ℝ))
    (hbad : (q : ℝ) ≤ ell * (b : ℝ)) :
    (b : ℝ) ≤ a * (N : ℝ) / (γ - ell) := by sorry
