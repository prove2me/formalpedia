-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_norm_le_iff_of_res
-- name    : ReciprocityTheory.ChartRestriction.L1.norm_le_iff_of_res
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:46:11.464247+00:00
-- url     : https://prove2.me/theorems/fbf37eb5-5e63-4b90-b97e-f35d1d14fdf8
-- title:
--   L1: norm le iff of res
-- statement:
--   The L1 construction uses the norm le iff of res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModLocD.lean#L54-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModLocD.lean#L54-L70

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModLocD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane Pointwise
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1

theorem ReciprocityTheory.ChartRestriction.L1.norm_le_iff_of_res {l : ℕ} [Fact l.Prime] (r : PadicAlgCl l →+* PadicAlgCl l)
    (hr : ∀ z : PadicAlgCl l, ‖z‖ ≤ 1 → ‖r z - z‖ < 1) (z : PadicAlgCl l) : ‖r z‖ ≤ 1 ↔ ‖z‖ ≤ 1 := by sorry
