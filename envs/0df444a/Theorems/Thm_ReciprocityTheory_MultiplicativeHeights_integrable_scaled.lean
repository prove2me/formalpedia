-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_integrable_scaled
-- name    : ReciprocityTheory.MultiplicativeHeights.integrable_scaled
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:04:19.967334+00:00
-- url     : https://prove2.me/theorems/18e96a12-7ce2-459e-b3b3-91903c6e18fc
-- title:
--   Multiplicative Heights: integrable scaled
-- statement:
--   The Multiplicative Heights construction uses the integrable scaled property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SphereTorusB.lean#L59-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SphereTorusB.lean#L59-L64

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereTorusA
import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereTorusB
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
open MeasureTheory

theorem ReciprocityTheory.MultiplicativeHeights.integrable_scaled {ι : Type} [Fintype ι] (hBasic : TorusMeanBasicStatement)
    (f : MvPolynomial ι ℂ) (hf : f ≠ 0) (r : ι → ℂ) (hr : ∀ j, r j ≠ 0) :
    Integrable (fun θ => Real.log ‖MvPolynomial.eval (fun j => r j * torusPoint θ j) f‖)
      (torusProb ι) := by sorry
