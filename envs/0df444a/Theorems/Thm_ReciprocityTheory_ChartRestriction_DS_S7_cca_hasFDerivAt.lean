-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_cca_hasFDerivAt
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.cca_hasFDerivAt
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:44:28.026953+00:00
-- url     : https://prove2.me/theorems/980ebd04-e932-4734-8261-47b44391682c
-- title:
--   S7: cca has FDeriv At
-- statement:
--   The S7 construction uses the cca has FDeriv At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CasChainA.lean#L50-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CasChainA.lean#L50-L77

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

theorem ReciprocityTheory.ChartRestriction.DS.S7.cca_hasFDerivAt [FiniteDimensional ℂ X] {F : X → E} {U : Set X} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) (hD : ContinuousOn (fderiv ℂ F) U) {κ a : ℝ → ℂ}
    (hκ : Continuous κ) (ha : Continuous a) {z₀ u : X} {δ : ℝ} (hδ : 0 < δ)
    (hsub : ∀ z ∈ closedBall z₀ δ, ∀ θ, z + a θ • u ∈ U) :
    HasFDerivAt (fun z => ∫ θ in (0 : ℝ)..2 * π, κ θ • F (z + a θ • u))
      (∫ θ in (0 : ℝ)..2 * π, κ θ • fderiv ℂ F (z₀ + a θ • u)) z₀ := by sorry
