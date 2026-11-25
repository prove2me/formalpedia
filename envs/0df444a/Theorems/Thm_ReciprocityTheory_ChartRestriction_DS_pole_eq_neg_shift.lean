-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_pole_eq_neg_shift
-- name    : ReciprocityTheory.ChartRestriction.DS.pole_eq_neg_shift
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:55:11.687405+00:00
-- url     : https://prove2.me/theorems/6bf0a355-39e0-5606-9dcc-be1ebf8750d3
-- title:
--   DS: pole eq neg shift
-- statement:
--   The DS construction uses the pole eq neg shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/Resolvent.lean#L59-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/Resolvent.lean#L59-L63

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_PartialTrace
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_GelfandHW
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Resolvent
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

theorem ReciprocityTheory.ChartRestriction.DS.pole_eq_neg_shift (μ : Fin n → ℝ) : poleV μ = -icShift (-μ) := by sorry
