-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_numRho_dot_root_right
-- name    : ReciprocityTheory.ChartRestriction.DS.numRho_dot_root_right
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:54:35.014191+00:00
-- url     : https://prove2.me/theorems/56abc859-56b2-597b-92a1-16105c3370f6
-- title:
--   DS: num Rho dot root right
-- statement:
--   The DS construction uses the num Rho dot root right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/NumRho.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/NumRho.lean#L18-L19

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

theorem ReciprocityTheory.ChartRestriction.DS.numRho_dot_root_right (a b : Fin n) (v : Fin n → ℝ) : dot v (root a b) = v a - v b := by sorry
