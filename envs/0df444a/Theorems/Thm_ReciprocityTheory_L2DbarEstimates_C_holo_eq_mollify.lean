-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_holo_eq_mollify
-- name    : ReciprocityTheory.L2DbarEstimates.C.holo_eq_mollify
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:54:38.302512+00:00
-- url     : https://prove2.me/theorems/a15b999a-68fd-4197-9f6d-ebf7578b5b13
-- title:
--   C: holo eq mollify
-- statement:
--   The C construction uses the holo eq mollify property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/IntegralMollProfBall.lean#L183-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/IntegralMollProfBall.lean#L183-L185

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_MeasurableEmbeddingRotAbout
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_IntegralBumpProfOnePos
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_IntegralMollProfBall
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
open scoped ENNReal

theorem ReciprocityTheory.L2DbarEstimates.C.holo_eq_mollify {n : ℕ} {f : V n → ℂ} {x : V n} {t : ℝ} (ht : 0 < t)
    (hf : DifferentiableOn ℂ f (closedBall x t)) : mollify n t f x = f x := by sorry
