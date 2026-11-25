-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slm_cd_adj
-- name    : ReciprocityTheory.ChartRestriction.DS.slm_cd_adj
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:54:14.813951+00:00
-- url     : https://prove2.me/theorems/f22be99a-2b7f-48c0-8687-3d2c91644c71
-- title:
--   DS: slm cd adj
-- statement:
--   The DS construction uses the slm cd adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CayleyChartDomainIsOpen.lean#L81-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CayleyChartDomainIsOpen.lean#L81-L94

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
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {k : WithTop ℕ∞}

theorem ReciprocityTheory.ChartRestriction.DS.slm_cd_adj {f : E → Matrix (Fin n) (Fin n) ℂ} (hf : ContDiffOn ℝ k f s) :
    ContDiffOn ℝ k (fun x => (f x).adjugate) s := by sorry
