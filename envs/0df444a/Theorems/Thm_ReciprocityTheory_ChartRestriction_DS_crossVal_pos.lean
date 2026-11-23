-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_crossVal_pos
-- name    : ReciprocityTheory.ChartRestriction.DS.crossVal_pos
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:13.961034+00:00
-- url     : https://prove2.me/theorems/b8e81ceb-18de-4f0e-9f77-efcaacc02157
-- title:
--   DS: cross Val pos
-- statement:
--   The DS construction uses the cross Val pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/Numerics.lean#L110-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/Numerics.lean#L110-L118

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

theorem ReciprocityTheory.ChartRestriction.DS.crossVal_pos {lam : Fin n → ℝ} (hmono : StrictAnti lam) {h : ℝ}
    (hh : GapAtLeast ε lam h) {a b : Fin n} (hab : a < b) (hε : ε a ≠ ε b) :
    2 * (h - n + 1) ≤
      casValK ε (lowK ε lam + root a b) - n - casValK ε (lowK ε lam) := by sorry
