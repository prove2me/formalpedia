-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slm_ret_cd
-- name    : ReciprocityTheory.ChartRestriction.DS.slm_ret_cd
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:54:54.280389+00:00
-- url     : https://prove2.me/theorems/df142460-1a64-4c45-ac12-3c7d3e06b148
-- title:
--   DS: slm ret cd
-- statement:
--   The DS construction uses the slm ret cd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CayleyChartDomainIsOpen.lean#L275-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CayleyChartDomainIsOpen.lean#L275-L281

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CayleyChartDomainIsOpen
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

theorem ReciprocityTheory.ChartRestriction.DS.slm_ret_cd (ε : Fin n → Bool) (g0 : Matrix (Fin n) (Fin n) ℂ) :
    ContDiffOn ℝ ∞ (slmRet ε g0) (slmV ε g0) := by sorry
