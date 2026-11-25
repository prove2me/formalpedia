-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_two_dot_rhoC_rhoN_le
-- name    : ReciprocityTheory.ChartRestriction.DS.two_dot_rhoC_rhoN_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:55:22.505575+00:00
-- url     : https://prove2.me/theorems/1b5d58cd-67e2-5a00-815a-388019a1e61e
-- title:
--   DS: two dot rho C rho N le
-- statement:
--   The DS construction uses the two dot rho C rho N le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/NumRho.lean#L134-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/NumRho.lean#L134-L173

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

theorem ReciprocityTheory.ChartRestriction.DS.two_dot_rhoC_rhoN_le (ε : Fin n → Bool) :
    2 * dot (rhoC ε) (rhoN ε) ≤ (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) := by sorry
