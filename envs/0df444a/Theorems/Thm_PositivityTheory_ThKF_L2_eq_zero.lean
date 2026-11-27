-- Prove2me | Theorems.Thm_PositivityTheory_ThKF_L2_eq_zero
-- name    : PositivityTheory.ThKF.L2.eq_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:00:13.262581+00:00
-- url     : https://prove2.me/theorems/5ac2f468-c9a5-5b89-8a90-c9055cf15943
-- title:
--   L2: eq zero
-- statement:
--   The L2 construction uses the eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/CartanFactorisation/IntegrableOnRight.lean#L46-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/CartanFactorisation/IntegrableOnRight.lean#L46-L66

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
omit [μ.IsMulRightInvariant]

theorem PositivityTheory.ThKF.L2.eq_zero (h : IsFundamentalDomain Γ 𝓕 μ) {f : G → ℂ} (hc : Continuous f) (hf : Inv Γ f)
    (f2 : IntegrableOn (fun x => ‖f x‖ ^ 2) 𝓕 μ) (h0 : ∫ x in 𝓕, conj (f x) * f x ∂μ = 0) : f = 0 := by sorry
