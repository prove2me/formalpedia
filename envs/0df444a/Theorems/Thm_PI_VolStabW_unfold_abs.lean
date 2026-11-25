-- Prove2me | Theorems.Thm_PI_VolStabW_unfold_abs
-- name    : PI.VolStabW.unfold_abs
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:44:09.625052+00:00
-- url     : https://prove2.me/theorems/78d6036c-abb6-4f8b-bdfa-85a88beac3ae
-- title:
--   Vol Stab W: unfold abs
-- statement:
--   The Vol Stab W construction uses the unfold abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/UnfoldAbsAlt.lean#L16-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/UnfoldAbsAlt.lean#L16-L180

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LintFibre
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_UnfoldAbsAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open MeasureTheory Set
open scoped ENNReal Pointwise
variable {G Y : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]
  [MulAction G Y] [MeasurableSpace Y]

theorem PI.VolStabW.unfold_abs {Γ H : Subgroup G} [Countable Γ]
    (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsInvInvariant]
    (μ' : Measure H) [μ'.IsMulLeftInvariant] [μ'.IsInvInvariant]
    (y0 : Y) (hH : ∀ k : G, k ∈ H ↔ k • y0 = y0)
    (ν : Measure Y) (Φ : Y → ℝ≥0∞) (hΦ : AEMeasurable Φ ν)
    (hΨ : Measurable fun g : G => Φ (g • y0))
    (hcov : ν {y | ¬ ∃ g : G, g • y0 = y} = 0)
    (hcomp : ∀ f : G → ℝ≥0∞, Measurable f → ∀ s : Y → G,
      (∀ y, (∃ g : G, g • y0 = y) → s y • y0 = y) →
      ∫⁻ g, f g ∂μ = ∫⁻ y, ∫⁻ k, f (s y * (k : G)) ∂μ' ∂ν)
    (𝓕 : Set G) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    (𝓕' : Set H) (h𝓕' : IsFundamentalDomain ((Γ ⊓ H).subgroupOf H) 𝓕' μ') :
    ∫⁻ h in 𝓕, ∑' x : orbS Γ y0, Φ (h⁻¹ • (x : Y)) ∂μ = μ' 𝓕' * ∫⁻ y, Φ y ∂ν := by sorry
