-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_red_norm_natCast
-- name    : ReciprocityTheory.ChartRestriction.L1.red_norm_natCast
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:49:01.120735+00:00
-- url     : https://prove2.me/theorems/e6c2b1a9-58f3-5dcd-86d9-bf46a22a7c84
-- title:
--   L1: red norm nat Cast
-- statement:
--   The L1 construction uses the red norm nat Cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedKur.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedKur.lean#L16-L17

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsTeichmullerRepModPrime
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KurComplete
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedKur
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
variable (l : ℕ) [Fact l.Prime]

theorem ReciprocityTheory.ChartRestriction.L1.red_norm_natCast {n : ℕ} (h : ¬ l ∣ n) : ‖(n : ℂ_[l])‖ = 1 := by sorry
