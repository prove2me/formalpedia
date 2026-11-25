-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_numRho_sum_opp
-- name    : ReciprocityTheory.ChartRestriction.DS.numRho_sum_opp
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:55:41.974845+00:00
-- url     : https://prove2.me/theorems/4d5f266f-c5d3-5b5c-9b67-afc2e1fac6c8
-- title:
--   DS: num Rho sum opp
-- statement:
--   The DS construction uses the num Rho sum opp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/NumRho.lean#L121-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/NumRho.lean#L121-L132

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_NumRho
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
variable {n : ℕ}
variable {ε : Fin n → Bool}

theorem ReciprocityTheory.ChartRestriction.DS.numRho_sum_opp (ε : Fin n → Bool) :
    (∑ a, ((univ.filter fun c => ε c ≠ ε a).card : ℝ)) = 2 * (pOf ε : ℝ) * (qOf ε : ℝ) := by sorry
