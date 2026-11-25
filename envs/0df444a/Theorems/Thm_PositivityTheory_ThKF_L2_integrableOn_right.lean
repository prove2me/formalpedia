-- Prove2me | Theorems.Thm_PositivityTheory_ThKF_L2_integrableOn_right
-- name    : PositivityTheory.ThKF.L2.integrableOn_right
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:03:53.4068+00:00
-- url     : https://prove2.me/theorems/9271a26a-8e2d-4e1b-abbb-e0a1d2343253
-- title:
--   L2: integrable On right
-- statement:
--   The L2 construction uses the integrable On right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/CartanFactorisation/IntegrableOnRight.lean#L26-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/CartanFactorisation/IntegrableOnRight.lean#L26-L30

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

theorem PositivityTheory.ThKF.L2.integrableOn_right {E : Type} [NormedAddCommGroup E] (h : IsFundamentalDomain Γ 𝓕 μ) (F : G → E)
    (hF : ∀ γ ∈ Γ, ∀ x, F (γ * x) = F x) (hi : IntegrableOn F 𝓕 μ) (g : G) : IntegrableOn (fun x => F (x * g)) 𝓕 μ := by sorry
