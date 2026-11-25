-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_SkodaOperators_pt_Gs
-- name    : ReciprocityTheory.L2DbarEstimates.H.SkodaOperators.pt_Gs
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:57:59.099794+00:00
-- url     : https://prove2.me/theorems/ab4fa316-67f1-45cd-90ac-e2bbd6db1b66
-- title:
--   Skoda Operators: pt Gs
-- statement:
--   The Skoda Operators construction uses the pt Gs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/IntegrableSliceProdFin.lean#L34-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/IntegrableSliceProdFin.lean#L34-L50

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

theorem ReciprocityTheory.L2DbarEstimates.H.SkodaOperators.pt_Gs {p : ℕ} (g : Fin p → ℂ) (w : ℂ) (c : ℝ) (hN : 0 < vsq g) :
    ∑ i, ‖w * (starRingEnd ℂ) (g i) / ((vsq g : ℝ) : ℂ)‖ ^ 2 * Real.exp (-c) =
      ‖w‖ ^ 2 * Real.exp (-(c + Real.log (vsq g))) := by sorry
