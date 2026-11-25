-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_dualPole_eq_neg_shift
-- name    : ReciprocityTheory.ChartRestriction.DS.dualPole_eq_neg_shift
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:49:34.839208+00:00
-- url     : https://prove2.me/theorems/5034f362-f866-4a1e-8f14-c1c767a8fadb
-- title:
--   DS: dual Pole eq neg shift
-- statement:
--   The DS construction uses the dual Pole eq neg shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/Resolvent.lean#L65-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/Resolvent.lean#L65-L69

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

theorem ReciprocityTheory.ChartRestriction.DS.dualPole_eq_neg_shift (μ : Fin n → ℝ) : poleVd μ = -icShift μ := by sorry
