-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_SkodaOperators_wint_G_le
-- name    : ReciprocityTheory.L2DbarEstimates.H.SkodaOperators.wint_G_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:57:22.169672+00:00
-- url     : https://prove2.me/theorems/f5d31484-bb98-4ac8-85eb-1bd07d233f6a
-- title:
--   Skoda Operators: wint G le
-- statement:
--   The Skoda Operators construction uses the wint G le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/IntegrableSliceProdFin.lean#L135-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/IntegrableSliceProdFin.lean#L135-L152

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
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]

theorem ReciprocityTheory.L2DbarEstimates.H.SkodaOperators.wint_G_le (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ) (g : Fin p → M → ℂ)
    (φ : M → ℝ) (hφ : Measurable φ) (hN : ∀ x, 0 < vsq (gv g x))
    (h : M × Fin p → ℂ) (hh : Measurable h) :
    wint n z (fun x => ∑ i, g i x * h (x, i)) (fun x => φ x + Real.log (vsq (gv g x))) ≤
      wint n (fun q : M × Fin p => z q.1) h (fun q => φ q.1) := by sorry
