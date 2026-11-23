-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_coefA_ofSum
-- name    : ReciprocityTheory.ChartRestriction.DS.coefA_ofSum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:09:43.314733+00:00
-- url     : https://prove2.me/theorems/c6317ad9-55cc-41c1-bdfa-8235fa3d65c8
-- title:
--   DS: coef A of Sum
-- statement:
--   The DS construction uses the coef A of Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CoefAInnerEqZero.lean#L157-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CoefAInnerEqZero.lean#L157-L202

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

theorem ReciprocityTheory.ChartRestriction.DS.coefA_ofSum {T : X →ₗ[ℂ] X} (hT : ∀ x y, inner ℂ (T x) y = inner ℂ x (T y))
    {TY : Y →ₗ[ℂ] Y} (hTY : ∀ x y, inner ℂ (TY x) y = inner ℂ x (TY y))
    {M' : Submodule ℂ X} (hloc : CoefLocFin T M') (ι : X →ₗ[ℂ] Y)
    (hιT : ∀ y ∈ M', ι (T y) = TY (ι y)) (hinj : ∀ y ∈ M', ι y = 0 → y = 0)
    (hfin : ∀ θ : ℝ, ∃ Z : Submodule ℂ X, FiniteDimensional ℂ Z ∧
      ∀ y ∈ M', T y = (θ : ℂ) • y → y ∈ Z) :
    ∀ z ∈ M', ∃ f ∈ M'.map ι, ∀ y ∈ M', inner ℂ f (ι y) = inner ℂ z y := by sorry
