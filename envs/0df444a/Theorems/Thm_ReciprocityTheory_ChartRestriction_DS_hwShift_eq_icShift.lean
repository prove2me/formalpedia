-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_hwShift_eq_icShift
-- name    : ReciprocityTheory.ChartRestriction.DS.hwShift_eq_icShift
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:51:14.905791+00:00
-- url     : https://prove2.me/theorems/9cd5ae82-d6d9-5e0c-b156-110cf70d281c
-- title:
--   DS: hw Shift eq ic Shift
-- statement:
--   The DS construction uses the hw Shift eq ic Shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/GelfandHW.lean#L14-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/GelfandHW.lean#L14-L20

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Gelfand
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_GelfandSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_GelfandHW
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

theorem ReciprocityTheory.ChartRestriction.DS.hwShift_eq_icShift (ν : Fin n → ℝ) : hwShift ν = icShift (ν + rho n) := by sorry
