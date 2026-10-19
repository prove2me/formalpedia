-- Prove2me | Theorems.Thm_SoficGroups_SourceCompressionRetainedDiscard_retained_missing_card_le_overlap_add_twice_rankChanging
-- name    : SoficGroups.SourceCompressionRetainedDiscard.retained_missing_card_le_overlap_add_twice_rankChanging
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:29.358829+00:00
-- url     : https://prove2.me/theorems/05463340-e3a7-48fe-9612-2c90eda7558b
-- title:
--   SoficGroups.SourceCompressionRetainedDiscard.retained_missing_card_le_overlap_add_twice_rankChanging
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceCompressionRetainedDiscard
open Filter Topology
open scoped BigOperators symmDiff

theorem SoficGroups.SourceCompressionRetainedDiscard.retained_missing_card_le_overlap_add_twice_rankChanging
    {V : Type*} [Fintype V] [DecidableEq V]
    (P Q : Finpartition (Finset.univ : Finset V))
    (T : Equiv.Perm V) (b : V → ℤ)
    (eta : ℝ) (heta : eta ≤ (1 : ℝ) / 2) :
    ((Finset.univ : Finset V) \
      SoficGroups.matchedRetainedSupport
        (retainedComponents P Q T b eta)).card ≤
      (∑ C ∈ SoficGroups.insufficientOverlapComponents P Q eta, C.card) +
        2 * (SoficGroups.RankArcCharging.rankChangingArc
          (Finset.univ : Finset V) b T.symm).card := by sorry
