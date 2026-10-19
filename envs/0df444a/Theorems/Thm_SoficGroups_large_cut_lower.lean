-- Prove2me | Theorems.Thm_SoficGroups_large_cut_lower
-- name    : SoficGroups.large_cut_lower
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:18.478977+00:00
-- url     : https://prove2.me/theorems/87df653d-e416-42bd-88eb-a7f5c5408bbb
-- title:
--   SoficGroups.large_cut_lower
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

theorem SoficGroups.large_cut_lower {γ ell a d N b e q : ℝ}
    (hgap : ell < γ) (hd : 0 ≤ d) (hN : 0 ≤ N)
    (hdeleted : (γ - ell) * b ≤ a * N)
    (hsmall : 2 * a * (2 * (γ - ell) + d) ≤ (γ - ell) ^ 2)
    (hlarge : N / 2 - b < e)
    (hcut : γ * e - a * N - d * b ≤ q) :
    ell * e ≤ q := by sorry
