-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_SkodaOperators_pt_G
-- name    : ReciprocityTheory.L2DbarEstimates.H.SkodaOperators.pt_G
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:58:39.704074+00:00
-- url     : https://prove2.me/theorems/af003782-cb2e-5a99-9178-cc2f1744f781
-- title:
--   Skoda Operators: pt G
-- statement:
--   The Skoda Operators construction uses the pt G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/IntegrableSliceProdFin.lean#L19-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/IntegrableSliceProdFin.lean#L19-L32

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_WeightedIntegralEqLintegral
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_IntegrableSliceProdFin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.H ReciprocityTheory.L2DbarEstimates.H.SkodaOperators
open MeasureTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.H
open scoped ENNReal InnerProductSpace
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.H.SkodaOperators.pt_G {p : ℕ} (g a : Fin p → ℂ) (c : ℝ) (hN : 0 < vsq g) :
    ‖∑ i, g i * a i‖ ^ 2 * Real.exp (-(c + Real.log (vsq g))) ≤
      ∑ i, ‖a i‖ ^ 2 * Real.exp (-c) := by sorry
