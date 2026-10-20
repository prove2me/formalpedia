-- Prove2me | Theorems.Thm_SoficGroups_maximumOverlapPart_overlap_of_not_mem_insufficient
-- name    : SoficGroups.maximumOverlapPart_overlap_of_not_mem_insufficient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:21.023082+00:00
-- url     : https://prove2.me/theorems/5b99238c-35b3-4331-9c28-418888e01a80
-- title:
--   SoficGroups.maximumOverlapPart_overlap_of_not_mem_insufficient
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

theorem SoficGroups.maximumOverlapPart_overlap_of_not_mem_insufficient
    {V : Type u} [DecidableEq V] {U : Finset V}
    (P Q : Finpartition U) (eta : ℝ) (C : Finset V)
    (hC : C ∈ P.parts)
    (hretained : C ∉ insufficientOverlapComponents P Q eta) :
    (1 - eta) * (C.card : ℝ) ≤
      ((C ∩ maximumOverlapPart Q C).card : ℝ) := by sorry
