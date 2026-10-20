-- Prove2me | Theorems.Thm_SoficGroups_matchedWordPreimageBad_card_le
-- name    : SoficGroups.matchedWordPreimageBad_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:19.258421+00:00
-- url     : https://prove2.me/theorems/feaba6bc-47f6-494b-a7b7-4261e6f1f7d3
-- title:
--   SoficGroups.matchedWordPreimageBad_card_le
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

theorem SoficGroups.matchedWordPreimageBad_card_le
    {V : Type*} [DecidableEq V]
    (U : Finset V) (R : Finset (Finset V))
    (D : Finset V → Finset V) (w : Equiv.Perm V) :
    (matchedWordPreimageBad U R D w).card ≤
      (U \ matchedCore R D).card := by sorry
