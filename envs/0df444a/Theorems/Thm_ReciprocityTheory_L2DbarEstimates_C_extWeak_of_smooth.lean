-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_extWeak_of_smooth
-- name    : ReciprocityTheory.L2DbarEstimates.C.extWeak_of_smooth
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:53:44.702273+00:00
-- url     : https://prove2.me/theorems/52b7eccb-a45d-5ae4-b494-503289d7cdca
-- title:
--   C: ext Weak of smooth
-- statement:
--   The C construction uses the ext Weak of smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtWeak.lean#L388-L413
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtWeak.lean#L388-L413

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCut
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeak
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_MollifyEqConvolution
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtWeakA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtWeak
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal ContDiff
variable {n : ℕ}

theorem ReciprocityTheory.L2DbarEstimates.C.extWeak_of_smooth {Ω : Set (V n)} {F u : V n → ℂ} (hΩ : IsOpen Ω)
    (hF : DifferentiableOn ℂ F Ω) (hsm : ∀ z ∈ Ω, ContDiffAt ℝ ∞ F z)
    (hu : DifferentiableOn ℂ u (Ω \ {z | F z = 0}))
    (hu2 : IntegrableOn (fun z => ‖u z‖ ^ 2) (Ω \ {z | F z = 0})) :
    WeakHolo Ω ((Ω \ {z | F z = 0}).indicator u) := by sorry
