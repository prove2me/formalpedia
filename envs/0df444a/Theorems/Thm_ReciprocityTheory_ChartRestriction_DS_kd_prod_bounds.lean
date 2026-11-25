-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_kd_prod_bounds
-- name    : ReciprocityTheory.ChartRestriction.DS.kd_prod_bounds
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:51:21.933603+00:00
-- url     : https://prove2.me/theorems/b47a7c9d-6a9e-5848-a2c1-dc1b057978c8
-- title:
--   DS: kd prod bounds
-- statement:
--   The DS construction uses the kd prod bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/HaarVolumes/KDensC.lean#L74-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/HaarVolumes/KDensC.lean#L74-L102

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_KDensC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {E₁ E₂ X₁ X₂ : Type*} [TopologicalSpace E₁] [PolishSpace E₁] [MeasurableSpace E₁] [BorelSpace E₁]
  [TopologicalSpace E₂] [PolishSpace E₂] [MeasurableSpace E₂] [BorelSpace E₂]
  [TopologicalSpace X₁] [T2Space X₁] [MeasurableSpace X₁] [BorelSpace X₁] [SecondCountableTopology X₁]
  [TopologicalSpace X₂] [T2Space X₂] [MeasurableSpace X₂] [BorelSpace X₂] [SecondCountableTopology X₂]

theorem ReciprocityTheory.ChartRestriction.DS.kd_prod_bounds {m₁ : Measure X₁} {m₂ : Measure X₂} [IsFiniteMeasure m₁] [IsFiniteMeasure m₂]
    (lam₁ : Measure E₁) (lam₂ : Measure E₂) [SigmaFinite lam₁] [SigmaFinite lam₂]
    {f₁ : E₁ → X₁} {f₂ : E₂ → X₂} {U₁ : Set E₁} {U₂ : Set E₂} (hU₁ : MeasurableSet U₁)
    (hU₂ : MeasurableSet U₂) (hf₁ : ContinuousOn f₁ U₁) (hf₂ : ContinuousOn f₂ U₂) (hi₁ : InjOn f₁ U₁)
    (hi₂ : InjOn f₂ U₂) (c₁ d₁ c₂ d₂ : ℝ≥0∞)
    (h₁ : ∀ A ⊆ U₁, MeasurableSet A → m₁ (f₁ '' A) ≤ c₁ * lam₁ A ∧ d₁ * lam₁ A ≤ m₁ (f₁ '' A))
    (h₂ : ∀ A ⊆ U₂, MeasurableSet A → m₂ (f₂ '' A) ≤ c₂ * lam₂ A ∧ d₂ * lam₂ A ≤ m₂ (f₂ '' A))
    {B : Set (E₁ × E₂)} (hB : MeasurableSet B) (hBU : B ⊆ U₁ ×ˢ U₂) :
    (m₁.prod m₂) (Prod.map f₁ f₂ '' B) ≤ c₁ * c₂ * (lam₁.prod lam₂) B ∧
      d₁ * d₂ * (lam₁.prod lam₂) B ≤ (m₁.prod m₂) (Prod.map f₁ f₂ '' B) := by sorry
