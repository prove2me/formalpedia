-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_GelfCpt_mul_entry
-- name    : PI.UnitaryGroupMassFormula.GelfCpt.mul_entry
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:38:19.193192+00:00
-- url     : https://prove2.me/theorems/166f9c42-1fd7-5a61-a0ab-6d6747974864
-- title:
--   Gelf Cpt: mul entry
-- statement:
--   The Gelf Cpt construction uses the mul entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompactGelfandAverage/IntegrableOfContinuousCpt.lean#L21-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompactGelfandAverage/IntegrableOfContinuousCpt.lean#L21-L53

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGelfandAverage_AvgStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGelfandAverage_IntegrableOfContinuousCpt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.GelfCpt
open MeasureTheory Matrix
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem PI.UnitaryGroupMassFormula.GelfCpt.mul_entry {N : ℕ} (μ : Measure G) [μ.IsHaarMeasure] (R : G → Matrix (Fin N) (Fin N) ℂ)
    (hR : ∀ i j, Continuous fun g => R g i j) (hRm : ∀ x y, R (x * y) = R x * R y)
    (f₁ f₂ : G → ℂ) (h₁ : Continuous f₁) (h₂ : Continuous f₂) (i j : Fin N) :
    ∑ k, (∫ x, f₁ x * R x i k ∂μ) * (∫ y, f₂ y * R y k j ∂μ) =
      ∫ z, (∫ x, f₁ x * f₂ (x⁻¹ * z) ∂μ) * R z i j ∂μ := by sorry
