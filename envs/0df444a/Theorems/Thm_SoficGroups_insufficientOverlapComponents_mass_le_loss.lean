-- Prove2me | Theorems.Thm_SoficGroups_insufficientOverlapComponents_mass_le_loss
-- name    : SoficGroups.insufficientOverlapComponents_mass_le_loss
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:21.023082+00:00
-- url     : https://prove2.me/theorems/f9ffef1f-0ea8-4296-bf7b-065e4c058b6d
-- title:
--   SoficGroups.insufficientOverlapComponents_mass_le_loss
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

theorem SoficGroups.insufficientOverlapComponents_mass_le_loss
    {V : Type u} [DecidableEq V] {U : Finset V}
    (P Q : Finpartition U) (eta : ℝ) :
    eta * (∑ C ∈ insufficientOverlapComponents P Q eta,
        (C.card : ℝ)) ≤
      ∑ C ∈ P.parts,
        ((C.card : ℝ) - ((C ∩ maximumOverlapPart Q C).card : ℝ)) := by sorry
