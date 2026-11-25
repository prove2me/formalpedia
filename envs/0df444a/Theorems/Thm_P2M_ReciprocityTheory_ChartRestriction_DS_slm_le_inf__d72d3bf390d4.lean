-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_slm_le_inf__d72d3bf390d4
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_slm_le_inf__d72d3bf390d4
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:12:40.719948+00:00
-- url     : https://prove2.me/theorems/a902534e-3ca5-43b0-8a45-620e6b09028c
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS slm le inf  d72d3bf390d4: P2 M Reciprocity Theory Chart Restriction DS slm le inf  d72d3bf390d4
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS slm le inf  d72d3bf390d4 construction uses the P2 M Reciprocity Theory Chart Restriction DS slm le inf  d72d3bf390d4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/ContDiffOnZeroOfContinuousOn.lean#L25-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/ContDiffOnZeroOfContinuousOn.lean#L25-L30

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CayleyChartDomainIsOpen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_ContDiffOnZeroOfContinuousOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Matrix
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool}
local notation "JJ" => Formalism.REAL.Jm

theorem P2M_ReciprocityTheory_ChartRestriction_DS_slm_le_inf__d72d3bf390d4 (N : ℕ) : (N : WithTop ℕ∞) ≤ ∞ := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«slm_le_inf'» := P2M_ReciprocityTheory_ChartRestriction_DS_slm_le_inf__d72d3bf390d4
