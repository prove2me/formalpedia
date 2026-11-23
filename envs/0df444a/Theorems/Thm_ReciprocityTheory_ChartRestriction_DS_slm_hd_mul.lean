-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slm_hd_mul
-- name    : ReciprocityTheory.ChartRestriction.DS.slm_hd_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:11:44.471816+00:00
-- url     : https://prove2.me/theorems/fb7abad1-427f-43a4-898b-1180a9072f40
-- title:
--   DS: slm hd mul
-- statement:
--   The DS construction uses the slm hd mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/ContDiffOnZeroOfContinuousOn.lean#L38-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/ContDiffOnZeroOfContinuousOn.lean#L38-L47

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

theorem ReciprocityTheory.ChartRestriction.DS.slm_hd_mul {f g : ℝ → Matrix (Fin n) (Fin n) ℂ} {f' g' : Matrix (Fin n) (Fin n) ℂ} {s : ℝ}
    (hf : HasDerivAt f f' s) (hg : HasDerivAt g g' s) :
    HasDerivAt (fun t => f t * g t) (f' * g s + f s * g') s := by sorry
