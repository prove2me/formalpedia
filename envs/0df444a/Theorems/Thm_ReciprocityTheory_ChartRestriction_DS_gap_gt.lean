-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_gap_gt
-- name    : ReciprocityTheory.ChartRestriction.DS.gap_gt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:52:49.893217+00:00
-- url     : https://prove2.me/theorems/1992a026-1d34-4a8b-aa4a-ab2e8bceab55
-- title:
--   DS: gap gt
-- statement:
--   The DS construction uses the gap gt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/Numerics.lean#L89-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/Numerics.lean#L89-L99

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_NumRho
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Numerics
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

theorem ReciprocityTheory.ChartRestriction.DS.gap_gt {a b : Fin n} (hε : ε a ≠ ε b) {h : ℝ}
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h) :
    2 * (n : ℝ) - 3 < h ∧ (n : ℝ) - 1 < h := by sorry
