-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rescale_neg_one_geometric_inv
-- name    : ReciprocityTheory.ChartRestriction.DS.rescale_neg_one_geometric_inv
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:54:01.3719+00:00
-- url     : https://prove2.me/theorems/707f5793-c1ef-4954-8358-6c66fbbe8e4c
-- title:
--   DS: rescale neg one geometric inv
-- statement:
--   The DS construction uses the rescale neg one geometric inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/Resolvent.lean#L31-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/Resolvent.lean#L31-L39

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

theorem ReciprocityTheory.ChartRestriction.DS.rescale_neg_one_geometric_inv (c : ℂ) :
    PowerSeries.rescale (-1 : ℂ) ((1 - PowerSeries.C c * PowerSeries.X)⁻¹) =
      (1 + PowerSeries.C c * PowerSeries.X)⁻¹ := by sorry
