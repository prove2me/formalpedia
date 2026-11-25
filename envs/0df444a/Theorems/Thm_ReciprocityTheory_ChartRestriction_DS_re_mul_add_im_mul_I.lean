-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_re_mul_add_im_mul_I
-- name    : ReciprocityTheory.ChartRestriction.DS.re_mul_add_im_mul_I
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:53:30.950703+00:00
-- url     : https://prove2.me/theorems/cff457d7-b6ba-58fb-91c3-aded6dd126a8
-- title:
--   DS: re mul add im mul I
-- statement:
--   The DS construction uses the re mul add im mul I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/ContDiffOnZeroOfContinuousOn.lean#L208-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/ContDiffOnZeroOfContinuousOn.lean#L208-L210

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
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.re_mul_add_im_mul_I (z c : ℂ) : (z.re : ℂ) * c + (z.im : ℂ) * (Complex.I * c) = c * z := by sorry
