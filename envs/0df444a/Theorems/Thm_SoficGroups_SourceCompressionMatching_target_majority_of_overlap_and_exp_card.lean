-- Prove2me | Theorems.Thm_SoficGroups_SourceCompressionMatching_target_majority_of_overlap_and_exp_card
-- name    : SoficGroups.SourceCompressionMatching.target_majority_of_overlap_and_exp_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.902902+00:00
-- url     : https://prove2.me/theorems/453a0586-f69b-4fc2-9c56-852841da426f
-- title:
--   SoficGroups.SourceCompressionMatching.target_majority_of_overlap_and_exp_card
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceCompressionMatching
open Filter Topology
open scoped BigOperators symmDiff

theorem SoficGroups.SourceCompressionMatching.target_majority_of_overlap_and_exp_card
    {V : Type*} [DecidableEq V]
    (C D : Finset V) (hC : C.Nonempty) (H eta : ℝ)
    (hoverlap :
      (1 - eta) * (C.card : ℝ) ≤ ((C ∩ D).card : ℝ))
    (hcard : (D.card : ℝ) < Real.exp H * (C.card : ℝ))
    (hsmall : 2 * (Real.exp H - 1 + 2 * eta) < 1) :
    D.card < 2 * (C ∩ D).card := by sorry
