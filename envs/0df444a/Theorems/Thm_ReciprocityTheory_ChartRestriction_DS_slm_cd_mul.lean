-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slm_cd_mul
-- name    : ReciprocityTheory.ChartRestriction.DS.slm_cd_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:18:00.932254+00:00
-- url     : https://prove2.me/theorems/bbfc328a-fc70-47fd-a0f5-4dfa084136fd
-- title:
--   DS: slm cd mul
-- statement:
--   The DS construction uses the slm cd mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CayleyChartDomainIsOpen.lean#L60-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CayleyChartDomainIsOpen.lean#L60-L65

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

theorem ReciprocityTheory.ChartRestriction.DS.slm_cd_mul {f g : E → Matrix (Fin n) (Fin n) ℂ} (hf : ContDiffOn ℝ k f s)
    (hg : ContDiffOn ℝ k g s) : ContDiffOn ℝ k (fun x => f x * g x) s := by sorry
