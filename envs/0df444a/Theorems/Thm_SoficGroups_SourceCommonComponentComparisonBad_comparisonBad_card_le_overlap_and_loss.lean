-- Prove2me | Theorems.Thm_SoficGroups_SourceCommonComponentComparisonBad_comparisonBad_card_le_overlap_and_loss
-- name    : SoficGroups.SourceCommonComponentComparisonBad.comparisonBad_card_le_overlap_and_loss
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:30.418361+00:00
-- url     : https://prove2.me/theorems/c885d816-bcfb-420e-97e9-b561e65e4b20
-- title:
--   SoficGroups.SourceCommonComponentComparisonBad.comparisonBad_card_le_overlap_and_loss
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

theorem SoficGroups.SourceCommonComponentComparisonBad.comparisonBad_card_le_overlap_and_loss
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : Finpartition (Finset.univ : Finset V))
    (T : Equiv.Perm V) (eta : ℝ) :
    (comparisonBad Q T eta).card ≤
      (∑ C ∈ SoficGroups.insufficientOverlapComponents
        (SoficGroups.transportedUnivFinpartition Q T) Q eta,
          C.card) +
      ∑ C ∈ (SoficGroups.transportedUnivFinpartition Q T).parts,
        (C \
          SoficGroups.maximumOverlapPart Q C).card := by sorry
