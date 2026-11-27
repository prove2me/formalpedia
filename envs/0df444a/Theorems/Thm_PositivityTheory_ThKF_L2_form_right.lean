-- Prove2me | Theorems.Thm_PositivityTheory_ThKF_L2_form_right
-- name    : PositivityTheory.ThKF.L2.form_right
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:00:35.809031+00:00
-- url     : https://prove2.me/theorems/12d0641e-843a-4b40-a81a-5850fe1eb398
-- title:
--   L2: form right
-- statement:
--   The L2 construction uses the form right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/CartanFactorisation/IntegrableOnRight.lean#L41-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/CartanFactorisation/IntegrableOnRight.lean#L41-L43

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

theorem PositivityTheory.ThKF.L2.form_right (h : IsFundamentalDomain Γ 𝓕 μ) {f g : G → ℂ} (hf : Inv Γ f) (hg : Inv Γ g) (a : G) :
    ∫ x in 𝓕, conj (f (x * a)) * g (x * a) ∂μ = ∫ x in 𝓕, conj (f x) * g x ∂μ := by sorry
