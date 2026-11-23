-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_G2_gap_gt
-- name    : ReciprocityTheory.ChartRestriction.DS.G2.gap_gt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:01:48.133695+00:00
-- url     : https://prove2.me/theorems/271f6679-7499-4b90-8974-3eca09066a21
-- title:
--   G2: gap gt
-- statement:
--   The G2 construction uses the gap gt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/ExceptionalGroupG2/BochnerG2/Numerics.lean#L92-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/ExceptionalGroupG2/BochnerG2/Numerics.lean#L92-L96

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Numerics
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_ExceptionalGroupG2_StdGap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_ExceptionalGroupG2_BochnerG2_Numerics
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_gap_gt

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.G2
variable {n : ℕ}
variable {ε : Fin n → Bool}

theorem ReciprocityTheory.ChartRestriction.DS.G2.gap_gt {a b : Fin n} (hε : ε a ≠ ε b) {h : ℝ}
    (hbig : 2 * (n : ℝ) < h) :
    2 * (n : ℝ) - 3 < h ∧ (n : ℝ) - 1 < h := by sorry
