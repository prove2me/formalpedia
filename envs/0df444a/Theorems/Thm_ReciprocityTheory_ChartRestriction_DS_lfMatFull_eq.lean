-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_lfMatFull_eq
-- name    : ReciprocityTheory.ChartRestriction.DS.lfMatFull_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:55:51.758062+00:00
-- url     : https://prove2.me/theorems/ec238caf-6a6e-50ee-ab0e-dd64e563fe91
-- title:
--   DS: lf Mat Full eq
-- statement:
--   The DS construction uses the lf Mat Full eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/LowFockB.lean#L43-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/LowFockB.lean#L43-L48

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockA
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.lfMatFull_eq (ε : Fin n → Bool) (a b : Fin n) : lfMatFull ε a b =
    if ε a = true ∧ ε b = true then ∑ x ∈ minusIdx ε, lfP a x * (lfP b x)ᵀ
    else if ε a = false ∧ ε b = false then -∑ i ∈ plusIdx ε, lfP i b * (lfP i a)ᵀ
    else 0 := by sorry
