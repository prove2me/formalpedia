-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slm_cd_iff
-- name    : ReciprocityTheory.ChartRestriction.DS.slm_cd_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:44:30.419703+00:00
-- url     : https://prove2.me/theorems/6ee30f72-c65a-4d35-a56b-cb62847824ea
-- title:
--   DS: slm cd iff
-- statement:
--   The DS construction uses the slm cd iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CayleyChartDomainIsOpen.lean#L57-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CayleyChartDomainIsOpen.lean#L57-L58

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

theorem ReciprocityTheory.ChartRestriction.DS.slm_cd_iff {f : E → Matrix (Fin n) (Fin n) ℂ} :
    ContDiffOn ℝ k f s ↔ ∀ i j, ContDiffOn ℝ k (fun x => f x i j) s := by sorry
