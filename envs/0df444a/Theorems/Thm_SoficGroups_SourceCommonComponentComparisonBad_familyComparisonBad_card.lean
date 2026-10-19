-- Prove2me | Theorems.Thm_SoficGroups_SourceCommonComponentComparisonBad_familyComparisonBad_card
-- name    : SoficGroups.SourceCommonComponentComparisonBad.familyComparisonBad_card
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:30.418361+00:00
-- url     : https://prove2.me/theorems/5a604e77-d829-4e04-96e7-01de076e1f03
-- title:
--   SoficGroups.SourceCommonComponentComparisonBad.familyComparisonBad_card
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

theorem SoficGroups.SourceCommonComponentComparisonBad.familyComparisonBad_card
    {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
    (Q : Finpartition (Finset.univ : Finset V))
    (p : ι → Equiv.Perm V) (eta : ℝ) :
    (familyComparisonBad Q p eta).card =
      ∑ i : ι, (comparisonBad Q (p i) eta).card := by sorry
