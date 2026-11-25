-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_tmLog_le
-- name    : ReciprocityTheory.MultiplicativeHeights.tmLog_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:05:15.735204+00:00
-- url     : https://prove2.me/theorems/92aac6f0-9781-4c72-9e67-2ec151ddc165
-- title:
--   Multiplicative Heights: tm Log le
-- statement:
--   The Multiplicative Heights construction uses the tm Log le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/TorusMeanC.lean#L19-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/TorusMeanC.lean#L19-L25

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanB
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Real Function
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem ReciprocityTheory.MultiplicativeHeights.tmLog_le (f : MvPolynomial ι ℂ) (θ : ι → ℝ) :
    tmLog f θ ≤ posLog (∑ s ∈ f.support, ‖f.coeff s‖) := by sorry
