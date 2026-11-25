-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMult_weightedHomogeneousComponent_mem_of_isMultiHomogIdeal_91ec1ac4e335
-- name    : P2M_GroundTheory_Heights__Heights_OrbitChartMult_weightedHomogeneousComponent_mem_of_isMultiHomogIdeal_91ec1ac4e335
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:38:19.225711+00:00
-- url     : https://prove2.me/theorems/f5d3ef87-2451-4631-94c7-f69040d394e1
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Chart Mult weighted Homogeneous Component mem of is Multi Homog Ideal 91ec1ac4e335: P2 M Ground Theory Heights  Heights Orbit Chart Mult weighted Homogeneous
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Chart Mult weighted Homogeneous Component mem of is Multi Homog Ideal 91ec1ac4e335 construction uses the P2 M Ground Theory Heights  Heights Orbit Chart Mult weighted Homogeneous Component mem of is Multi Homog Ideal 91ec1ac4e335 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMultLemmas.lean#L122-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMultLemmas.lean#L122-L131

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
attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem P2M_GroundTheory_Heights__Heights_OrbitChartMult_weightedHomogeneousComponent_mem_of_isMultiHomogIdeal_91ec1ac4e335
    {V : Ideal (MvPolynomial (Coord n) ℤ)} (hV : Geo.IsMultiHomogIdeal (ι := blockIdx n) V)
    {v : MvPolynomial (Coord n) ℤ} (hv : v ∈ V) (e : ι → ℕ) :
    weightedHomogeneousComponent (coordDeg n) e v ∈ V := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitChartMult».«weightedHomogeneousComponent_mem_of_isMultiHomogIdeal» := P2M_GroundTheory_Heights__Heights_OrbitChartMult_weightedHomogeneousComponent_mem_of_isMultiHomogIdeal_91ec1ac4e335
