-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rescale_neg_one_const
-- name    : ReciprocityTheory.ChartRestriction.DS.rescale_neg_one_const
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:55:32.896586+00:00
-- url     : https://prove2.me/theorems/bf8d97f6-7007-54d9-8087-acad06b2357f
-- title:
--   DS: rescale neg one const
-- statement:
--   The DS construction uses the rescale neg one const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/Resolvent.lean#L23-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/Resolvent.lean#L23-L29

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

theorem ReciprocityTheory.ChartRestriction.DS.rescale_neg_one_const (c : ℂ) :
    PowerSeries.rescale (-1 : ℂ) (PowerSeries.C c) = PowerSeries.C c := by sorry
