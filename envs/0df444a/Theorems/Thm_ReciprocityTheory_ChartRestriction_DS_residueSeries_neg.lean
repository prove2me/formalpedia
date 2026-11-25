-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_residueSeries_neg
-- name    : ReciprocityTheory.ChartRestriction.DS.residueSeries_neg
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:57:15.009693+00:00
-- url     : https://prove2.me/theorems/8fe5e8b6-296b-55c6-a5bb-724ff6bbe887
-- title:
--   DS: residue Series neg
-- statement:
--   The DS construction uses the residue Series neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/Resolvent.lean#L41-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/Resolvent.lean#L41-L51

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

theorem ReciprocityTheory.ChartRestriction.DS.residueSeries_neg (l : Fin n → ℂ) :
    resSeries (-l) = -PowerSeries.rescale (-1 : ℂ) (gelfandSeries l) := by sorry
