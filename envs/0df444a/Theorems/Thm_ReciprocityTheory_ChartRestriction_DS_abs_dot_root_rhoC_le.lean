-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_abs_dot_root_rhoC_le
-- name    : ReciprocityTheory.ChartRestriction.DS.abs_dot_root_rhoC_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:49:47.26904+00:00
-- url     : https://prove2.me/theorems/1e56c235-b545-4ccb-8ca1-bbecd6109ecf
-- title:
--   DS: abs dot root rho C le
-- statement:
--   The DS construction uses the abs dot root rho C le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/NumRho.lean#L55-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/NumRho.lean#L55-L72

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

theorem ReciprocityTheory.ChartRestriction.DS.abs_dot_root_rhoC_le {a b : Fin n} (hε : ε a ≠ ε b) :
    |dot (root a b) (rhoC ε)| ≤ ((n : ℝ) - 2) / 2 := by sorry
