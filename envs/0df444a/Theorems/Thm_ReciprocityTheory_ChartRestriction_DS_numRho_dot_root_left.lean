-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_numRho_dot_root_left
-- name    : ReciprocityTheory.ChartRestriction.DS.numRho_dot_root_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:12:09.585201+00:00
-- url     : https://prove2.me/theorems/01b22023-34c0-403d-b2a5-39c7e057b582
-- title:
--   DS: num Rho dot root left
-- statement:
--   The DS construction uses the num Rho dot root left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/NumRho.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/NumRho.lean#L15-L16

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

theorem ReciprocityTheory.ChartRestriction.DS.numRho_dot_root_left (a b : Fin n) (v : Fin n → ℝ) : dot (root a b) v = v a - v b := by sorry
