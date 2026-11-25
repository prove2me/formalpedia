-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_csq_filter_eq_minus
-- name    : ReciprocityTheory.ChartRestriction.DS.csq_filter_eq_minus
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:50:10.016284+00:00
-- url     : https://prove2.me/theorems/1c115ef5-a57b-5e6b-ac8e-f4979eb969d6
-- title:
--   DS: csq filter eq minus
-- statement:
--   The DS construction uses the csq filter eq minus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARSqA.lean#L35-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARSqA.lean#L35-L39

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CarSumSqZeroOfAnti
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARSqA
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
variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem ReciprocityTheory.ChartRestriction.DS.csq_filter_eq_minus (ε : Fin n → Bool) {a : Fin n} (ha : a ∈ minusIdx ε) :
    univ.filter (fun b => ε b = ε a) = minusIdx ε := by sorry
