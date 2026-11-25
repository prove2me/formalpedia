-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_ev_pos_of_not_mem_zeroSet
-- name    : ReciprocityTheory.L2DbarEstimates.I.ev_pos_of_not_mem_zeroSet
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:57:34.772774+00:00
-- url     : https://prove2.me/theorems/618fecd1-2d91-5e27-a116-090e0d9f04f4
-- title:
--   I: ev pos of not mem zero Set
-- statement:
--   The I construction uses the ev pos of not mem zero Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/LocallyCompactSpaceOfIsLocalHomeomorph.lean#L40-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/LocallyCompactSpaceOfIsLocalHomeomorph.lean#L40-L46

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ChartSymmEventuallyEq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LocallyCompactSpaceOfIsLocalHomeomorph
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff

theorem ReciprocityTheory.L2DbarEstimates.I.ev_pos_of_not_mem_zeroSet {M : Type*} (n : ℕ) (g : Fin n → M → ℂ) (ph : M → ℝ)
    (r : ℝ) (hr : 0 < r) (x : M) (hx : x ∉ zeroSet n g) : 0 < ev n g ph r x := by sorry
