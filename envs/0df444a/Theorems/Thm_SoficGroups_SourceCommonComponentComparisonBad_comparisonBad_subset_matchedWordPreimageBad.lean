-- Prove2me | Theorems.Thm_SoficGroups_SourceCommonComponentComparisonBad_comparisonBad_subset_matchedWordPreimageBad
-- name    : SoficGroups.SourceCommonComponentComparisonBad.comparisonBad_subset_matchedWordPreimageBad
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:30.418361+00:00
-- url     : https://prove2.me/theorems/09443ebf-7f20-45e3-ac48-d736eca180a0
-- title:
--   SoficGroups.SourceCommonComponentComparisonBad.comparisonBad_subset_matchedWordPreimageBad
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceCommonComponentComparisonBad
open Filter Topology
open scoped BigOperators

theorem SoficGroups.SourceCommonComponentComparisonBad.comparisonBad_subset_matchedWordPreimageBad
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : Finpartition (Finset.univ : Finset V))
    (T : Equiv.Perm V) (eta : ℝ) :
    comparisonBad Q T eta ⊆
      SoficGroups.matchedWordPreimageBad
        (Finset.univ : Finset V)
        (overlapRetainedComponents Q T eta)
        (SoficGroups.maximumOverlapPart Q) T := by sorry
