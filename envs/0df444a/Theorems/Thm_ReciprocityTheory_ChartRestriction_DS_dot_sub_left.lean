-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_dot_sub_left
-- name    : ReciprocityTheory.ChartRestriction.DS.dot_sub_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:46.666032+00:00
-- url     : https://prove2.me/theorems/0ea7a8ac-c6b8-40ac-9ac5-21ae41ad8e3c
-- title:
--   DS: dot sub left
-- statement:
--   The DS construction uses the dot sub left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFPrimeB.lean#L58-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFPrimeB.lean#L58-L59

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerWeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem ReciprocityTheory.ChartRestriction.DS.dot_sub_left (u v w : Fin n → ℝ) : dot (u - v) w = dot u w - dot v w := by sorry
