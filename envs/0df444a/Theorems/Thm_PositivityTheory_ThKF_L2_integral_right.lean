-- Prove2me | Theorems.Thm_PositivityTheory_ThKF_L2_integral_right
-- name    : PositivityTheory.ThKF.L2.integral_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:53:03.008799+00:00
-- url     : https://prove2.me/theorems/6f3ecb50-7273-44dc-b453-f1511da65a3b
-- title:
--   L2: integral right
-- statement:
--   The L2 construction uses the integral right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/CartanFactorisation/IntegrableOnRight.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/CartanFactorisation/IntegrableOnRight.lean#L21-L24

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_CartanFactorisation_IntegrableOnRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKF PositivityTheory.ThKF.L2
open MeasureTheory
open scoped ComplexConjugate Pointwise
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {Γ : Subgroup G} [Countable Γ] {𝓕 : Set G}

theorem PositivityTheory.ThKF.L2.integral_right {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (h : IsFundamentalDomain Γ 𝓕 μ) (F : G → E)
    (hF : ∀ γ ∈ Γ, ∀ x, F (γ * x) = F x) (g : G) : ∫ x in 𝓕, F (x * g) ∂μ = ∫ x in 𝓕, F x ∂μ := by sorry
