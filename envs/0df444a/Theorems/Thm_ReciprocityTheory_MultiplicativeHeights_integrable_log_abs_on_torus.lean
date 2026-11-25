-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_integrable_log_abs_on_torus
-- name    : ReciprocityTheory.MultiplicativeHeights.integrable_log_abs_on_torus
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:04:11.051734+00:00
-- url     : https://prove2.me/theorems/e8ff6a3d-2305-4a16-a9bd-5e8e71a0d7f3
-- title:
--   Multiplicative Heights: integrable log abs on torus
-- statement:
--   The Multiplicative Heights construction uses the integrable log abs on torus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/TorusMeanD.lean#L46-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/TorusMeanD.lean#L46-L77

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanC
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanD
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

theorem ReciprocityTheory.MultiplicativeHeights.integrable_log_abs_on_torus (S : Finset ι) :
    ∀ f : MvPolynomial ι ℂ, f.vars ⊆ S → Integrable (tmLog f) (torusProb ι) := by sorry
