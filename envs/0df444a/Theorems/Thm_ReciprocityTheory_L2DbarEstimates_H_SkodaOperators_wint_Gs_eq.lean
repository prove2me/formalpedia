-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_SkodaOperators_wint_Gs_eq
-- name    : ReciprocityTheory.L2DbarEstimates.H.SkodaOperators.wint_Gs_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:04:34.108092+00:00
-- url     : https://prove2.me/theorems/dd1f1953-953a-439c-9b92-185dc9b33a19
-- title:
--   Skoda Operators: wint Gs eq
-- statement:
--   The Skoda Operators construction uses the wint Gs eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/IntegrableSliceProdFin.lean#L154-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/IntegrableSliceProdFin.lean#L154-L188

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

theorem ReciprocityTheory.L2DbarEstimates.H.SkodaOperators.wint_Gs_eq (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ) (g : Fin p → M → ℂ)
    (hg : ∀ l, Measurable (g l)) (φ : M → ℝ) (hφ : Measurable φ) (hN : ∀ x, 0 < vsq (gv g x))
    (w : M → ℂ) (hw : Measurable w) :
    wint n (fun q : M × Fin p => z q.1)
        (fun q => w q.1 * (starRingEnd ℂ) (g q.2 q.1) / ((vsq (gv g q.1) : ℝ) : ℂ))
        (fun q => φ q.1) =
      wint n z w (fun x => φ x + Real.log (vsq (gv g x))) := by sorry
