-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_kap_unit
-- name    : ReciprocityTheory.ChartRestriction.L1.kap_unit
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:44:16.284697+00:00
-- url     : https://prove2.me/theorems/9999812a-a570-4a73-84e2-55b7fa62b78c
-- title:
--   L1: kap unit
-- statement:
--   The L1 construction uses the kap unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/KapUnit.lean#L7-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/KapUnit.lean#L7-L71

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KapUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1

theorem ReciprocityTheory.ChartRestriction.L1.kap_unit {K : Type} [NormedField K] [IsUltrametricDist K] (g2 g3 e : K) (h2 : ‖g2‖ ≤ 1)
    (h3 : ‖g3‖ ≤ 1) (hΔ : ‖g2 ^ 3 - 27 * g3 ^ 2‖ = 1) (h22 : ‖(2 : K)‖ = 1)
    (he : 4 * e ^ 3 - g2 * e - g3 = 0) : ‖e‖ ≤ 1 ∧ ‖3 * e ^ 2 - g2 / 4‖ = 1 := by sorry
