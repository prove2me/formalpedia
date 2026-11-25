-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_CasPsA_sum_sum_sum_sum_comm
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.CasPsA.sum_sum_sum_sum_comm
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:47:41.173702+00:00
-- url     : https://prove2.me/theorems/9212a45e-4098-5a67-9f54-eaa2d12f8647
-- title:
--   Cas Ps A: sum sum sum sum comm
-- statement:
--   The Cas Ps A construction uses the sum sum sum sum comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CasPsA.lean#L37-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CasPsA.lean#L37-L45

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasPsA
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS.S7.CasPsA
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.S7.CasPsA.sum_sum_sum_sum_comm (f : Fin n → Fin n → Fin n → Fin n → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by sorry
