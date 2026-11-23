-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_cca_bounds
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.cca_bounds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:05:35.264796+00:00
-- url     : https://prove2.me/theorems/5774a8a5-6b07-4726-9da3-fad9c14c9740
-- title:
--   S7: cca bounds
-- statement:
--   The S7 construction uses the cca bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CasChainA.lean#L17-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CasChainA.lean#L17-L31

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasChainA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Metric Set Filter Topology MeasureTheory Complex
open scoped ContDiff Real
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem ReciprocityTheory.ChartRestriction.DS.S7.cca_bounds {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ X]
    {F : X → G} {U : Set X} (hF : ContinuousOn F U) {κ a : ℝ → ℂ} (hκ : Continuous κ)
    (ha : Continuous a) {z₀ u : X} {δ : ℝ} (hsub : ∀ z ∈ closedBall z₀ δ, ∀ θ, z + a θ • u ∈ U) :
    ∃ B : ℝ, ∀ z ∈ closedBall z₀ δ, ∀ θ ∈ Set.uIoc (0 : ℝ) (2 * π), ‖κ θ • F (z + a θ • u)‖ ≤ B := by sorry
