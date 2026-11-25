-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_cca_fderiv_eq
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.cca_fderiv_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:44:25.213895+00:00
-- url     : https://prove2.me/theorems/1576b318-b2aa-5bdc-bba5-a437fe3c5f4e
-- title:
--   S7: cca fderiv eq
-- statement:
--   The S7 construction uses the cca fderiv eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CasChainA.lean#L106-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CasChainA.lean#L106-L127

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

theorem ReciprocityTheory.ChartRestriction.DS.S7.cca_fderiv_eq [CompleteSpace E] {F : X → E} {U : Set X} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) {z u : X} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : ∀ t ∈ closedBall (0 : ℂ) ρ, z + t • u ∈ U) :
    fderiv ℂ F z u = (2 * π * I)⁻¹ •
      ∫ θ in (0 : ℝ)..2 * π, ccaKappa ρ θ • F (z + circleMap 0 ρ θ • u) := by sorry
