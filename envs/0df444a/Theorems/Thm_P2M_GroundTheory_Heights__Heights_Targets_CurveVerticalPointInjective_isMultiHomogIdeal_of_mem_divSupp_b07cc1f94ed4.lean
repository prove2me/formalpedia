-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointInjective_isMultiHomogIdeal_of_mem_divSupp_b07cc1f94ed4
-- name    : P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointInjective_isMultiHomogIdeal_of_mem_divSupp_b07cc1f94ed4
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:10:50.921242+00:00
-- url     : https://prove2.me/theorems/b4afbb88-ef48-53d3-b373-57e290ff30ea
-- title:
--   P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Injective is Multi Homog Ideal of mem div Supp b07cc1f94ed4: P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Injective
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Injective is Multi Homog Ideal of mem div Supp b07cc1f94ed4 construction uses the P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Injective is Multi Homog Ideal of mem div Supp b07cc1f94ed4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveVertPointInj.lean#L23-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveVertPointInj.lean#L23-L32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveVertPointLengthSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_OfSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCurveVertPointInj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
open GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointInjective
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointInjective_isMultiHomogIdeal_of_mem_divSupp_b07cc1f94ed4 (y : (Σ k, ι k) → Ω) (s : MRing ι) (d : K → ℕ)
    (hA : IsArithVar (mCoordIdeal y) 1) (hs : IsMultiHomog s d) {W : Ideal (MRing ι)}
    (hW : W ∈ divSupp (mCoordIdeal y) s) : IsMultiHomogIdeal W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«CurveVerticalPointInjective».«isMultiHomogIdeal_of_mem_divSupp» := P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointInjective_isMultiHomogIdeal_of_mem_divSupp_b07cc1f94ed4
