-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_SkodaOperators_ae_lift_prodFin
-- name    : ReciprocityTheory.L2DbarEstimates.H.SkodaOperators.ae_lift_prodFin
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:57:33.746563+00:00
-- url     : https://prove2.me/theorems/ed63968a-bef3-5c41-98e2-3e473a245f5c
-- title:
--   Skoda Operators: ae lift prod Fin
-- statement:
--   The Skoda Operators construction uses the ae lift prod Fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/IntegrableSliceProdFin.lean#L122-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/IntegrableSliceProdFin.lean#L122-L128

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

theorem ReciprocityTheory.L2DbarEstimates.H.SkodaOperators.ae_lift_prodFin (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ) {P : M → Prop}
    (hP : ∀ᵐ x ∂vol n z, P x) : ∀ᵐ q ∂vol n (fun q : M × Fin p => z q.1), P q.1 := by sorry
