-- Prove2me | Theorems.Thm_SoficGroups_matchedRadiusBad_card_le
-- name    : SoficGroups.matchedRadiusBad_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:21.023082+00:00
-- url     : https://prove2.me/theorems/5710d389-9d72-44ea-ae6e-6525a4c59361
-- title:
--   SoficGroups.matchedRadiusBad_card_le
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

theorem SoficGroups.matchedRadiusBad_card_le
    {V ι : Type*} [DecidableEq V] {U : Finset V}
    (P : Finpartition U) (I : Finset ι) (w : ι → Equiv.Perm V)
    (B : Finset V) :
    (U ∩ matchedRadiusBad P I w B).card ≤
      (U ∩ B).card +
        ∑ i ∈ I, (partitionWordCrossing P (w i)).card := by sorry
