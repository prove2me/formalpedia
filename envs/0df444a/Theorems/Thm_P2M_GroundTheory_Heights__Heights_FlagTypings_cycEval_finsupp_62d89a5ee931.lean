-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FlagTypings_cycEval_finsupp_62d89a5ee931
-- name    : P2M_GroundTheory_Heights__Heights_FlagTypings_cycEval_finsupp_62d89a5ee931
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:20:33.191374+00:00
-- url     : https://prove2.me/theorems/30ae3e44-7d88-531b-8b1b-c46c4bd5fe4f
-- title:
--   P2 M Ground Theory Heights  Heights Flag Typings cyc Eval finsupp 62d89a5ee931: P2 M Ground Theory Heights  Heights Flag Typings cyc Eval finsupp 62d89a5ee931
-- statement:
--   The P2 M Ground Theory Heights  Heights Flag Typings cyc Eval finsupp 62d89a5ee931 construction uses the P2 M Ground Theory Heights  Heights Flag Typings cyc Eval finsupp 62d89a5ee931 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/IsVerticalDivOfIsVerticalDivisor.lean#L209-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/IsVerticalDivOfIsVerticalDivisor.lean#L209-L218

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_TrivBundleIsTwistedForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FlagTypings
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
set_option linter.unusedSectionVars false
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_FlagTypings_cycEval_finsupp_62d89a5ee931 {R : Type*} [CommRing R] (n : Ideal (MRingOver R ι) → ℤ)
    (Z : Ideal (MRingOver R ι) →₀ ℤ) : NumbersDVR.cycEval n ⇑Z = Z.sum fun W c => c * n W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FlagTypings».«cycEval_finsupp» := P2M_GroundTheory_Heights__Heights_FlagTypings_cycEval_finsupp_62d89a5ee931
