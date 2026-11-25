-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_integrableOn_mul_of_sq
-- name    : ReciprocityTheory.L2DbarEstimates.C.integrableOn_mul_of_sq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:54:26.706357+00:00
-- url     : https://prove2.me/theorems/e1aeb776-6a2b-5800-9c83-b5748747c1c7
-- title:
--   C: integrable On mul of sq
-- statement:
--   The C construction uses the integrable On mul of sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtWeak.lean#L24-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtWeak.lean#L24-L37

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

theorem ReciprocityTheory.L2DbarEstimates.C.integrableOn_mul_of_sq {W : Set (V n)} {u h : V n → ℂ}
    (hum : AEStronglyMeasurable u (volume.restrict W)) (hu2 : IntegrableOn (fun z => ‖u z‖ ^ 2) W)
    (hc : Continuous h) (hs : HasCompactSupport h) : IntegrableOn (fun z => u z * h z) W := by sorry
