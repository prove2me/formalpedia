-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMult_chartCone_of_isWeightedHomogeneous_c74b1368637f
-- name    : P2M_GroundTheory_Heights__Heights_OrbitChartMult_chartCone_of_isWeightedHomogeneous_c74b1368637f
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:36:22.122455+00:00
-- url     : https://prove2.me/theorems/895a6758-e50b-511b-a16d-92dff4aab3e6
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Chart Mult chart Cone of is Weighted Homogeneous c74b1368637f: P2 M Ground Theory Heights  Heights Orbit Chart Mult chart Cone of is Weighted Homogeneous c74b
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Chart Mult chart Cone of is Weighted Homogeneous c74b1368637f construction uses the P2 M Ground Theory Heights  Heights Orbit Chart Mult chart Cone of is Weighted Homogeneous c74b1368637f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMultLemmas.lean#L48-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMultLemmas.lean#L48-L70

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartMult
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMultLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.OrbitChartMult
variable {ι : Type} {n : ι → ℕ}
variable (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
variable [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_OrbitChartMult_chartCone_of_isWeightedHomogeneous_c74b1368637f (D : Type*) [CommRing D] [Algebra (chartRing x c) D]
    {F : MvPolynomial (Coord n) ℤ} {d : ι → ℕ} (hF : IsWeightedHomogeneous (coordDeg n) F d) :
    chartCone x c D F = C (algebraMap (chartRing x c) D (chartEval x c F)) * ∏ k, X k ^ d k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitChartMult».«chartCone_of_isWeightedHomogeneous» := P2M_GroundTheory_Heights__Heights_OrbitChartMult_chartCone_of_isWeightedHomogeneous_c74b1368637f
