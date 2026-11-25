-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slm_hd_conjT
-- name    : ReciprocityTheory.ChartRestriction.DS.slm_hd_conjT
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:53:59.315982+00:00
-- url     : https://prove2.me/theorems/bbbdc583-389a-5355-8cf5-1e6b43a8e82e
-- title:
--   DS: slm hd conj T
-- statement:
--   The DS construction uses the slm hd conj T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/ContDiffOnZeroOfContinuousOn.lean#L49-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/ContDiffOnZeroOfContinuousOn.lean#L49-L53

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

theorem ReciprocityTheory.ChartRestriction.DS.slm_hd_conjT {f : ℝ → Matrix (Fin n) (Fin n) ℂ} {f' : Matrix (Fin n) (Fin n) ℂ} {s : ℝ}
    (hf : HasDerivAt f f' s) : HasDerivAt (fun t => (f t)ᴴ) f'ᴴ s := by sorry
