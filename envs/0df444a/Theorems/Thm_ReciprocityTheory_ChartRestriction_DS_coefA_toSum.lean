-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_coefA_toSum
-- name    : ReciprocityTheory.ChartRestriction.DS.coefA_toSum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:29.749278+00:00
-- url     : https://prove2.me/theorems/1bd54823-7206-4975-ae8e-72c49aa163e4
-- title:
--   DS: coef A to Sum
-- statement:
--   The DS construction uses the coef A to Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CoefAInnerEqZero.lean#L87-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CoefAInnerEqZero.lean#L87-L110

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CoefAInnerEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]

theorem ReciprocityTheory.ChartRestriction.DS.coefA_toSum {T : X →ₗ[ℂ] X} (hT : ∀ x y, inner ℂ (T x) y = inner ℂ x (T y))
    {M' : Submodule ℂ X} (hloc : CoefLocFin T M') (ℓ : X →ₗ[ℂ] ℂ) (C : ℝ)
    {Z₀ : Submodule ℂ X} (hZ₀ : FiniteDimensional ℂ Z₀) (hZM : Z₀ ≤ M')
    (hlow : ∀ y ∈ M', ∀ θ : ℝ, θ ≤ C → T y = (θ : ℂ) • y → y ∈ Z₀)
    (hhigh : ∀ y ∈ M', ∀ θ : ℝ, C < θ → T y = (θ : ℂ) • y → ℓ y = 0) :
    ∃ z ∈ M', ∀ y ∈ M', inner ℂ z y = ℓ y := by sorry
