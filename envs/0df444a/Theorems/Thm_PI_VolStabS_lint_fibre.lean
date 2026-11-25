-- Prove2me | Theorems.Thm_PI_VolStabS_lint_fibre
-- name    : PI.VolStabS.lint_fibre
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:36:46.052188+00:00
-- url     : https://prove2.me/theorems/90c1c674-145f-4942-a661-3d078b0aa446
-- title:
--   Vol Stab S: lint fibre
-- statement:
--   The Vol Stab S construction uses the lint fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/LintFibre.lean#L16-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/LintFibre.lean#L16-L67

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_UnfoldAbs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LintFibre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabS
open MeasureTheory Set
open scoped ENNReal Pointwise
variable {G Y : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]
  [MulAction G Y]

theorem PI.VolStabS.lint_fibre {Γ H : Subgroup G} [Countable Γ] (μ' : Measure H) [μ'.IsMulLeftInvariant]
    [μ'.IsInvInvariant] (y0 : Y) (hH : ∀ k : G, k ∈ H ↔ k • y0 = y0) [Countable (orbS Γ y0)]
    {A : Set G} (hA : MeasurableSet A)
    (𝓕' : Set H) (h𝓕' : IsFundamentalDomain ((Γ ⊓ H).subgroupOf H) 𝓕' μ')
    (ρ : G → ℝ≥0∞) (hρ : Measurable ρ) (hρi : ∀ γ ∈ Γ, ∀ g, ρ (γ * g) = ρ g) (s : G) :
    ∫⁻ k, cfun Γ A y0 (s * (k : G)) * ρ ((s * (k : G))⁻¹) ∂μ' =
      ∫⁻ k in 𝓕', cntN Γ A ((k : G) * s⁻¹) * ρ ((k : G) * s⁻¹) ∂μ' := by sorry
