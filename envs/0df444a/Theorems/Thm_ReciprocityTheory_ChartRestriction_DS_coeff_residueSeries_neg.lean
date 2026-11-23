-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_coeff_residueSeries_neg
-- name    : ReciprocityTheory.ChartRestriction.DS.coeff_residueSeries_neg
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:30.288649+00:00
-- url     : https://prove2.me/theorems/83210e0d-60d4-478c-b1e7-32461d50f548
-- title:
--   DS: coeff residue Series neg
-- statement:
--   The DS construction uses the coeff residue Series neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/Resolvent.lean#L53-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/Resolvent.lean#L53-L57

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

theorem ReciprocityTheory.ChartRestriction.DS.coeff_residueSeries_neg (l : Fin n → ℂ) (k : ℕ) :
    PowerSeries.coeff (k + 1) (resSeries (-l)) = (-1 : ℂ) ^ k * gval l k := by sorry
