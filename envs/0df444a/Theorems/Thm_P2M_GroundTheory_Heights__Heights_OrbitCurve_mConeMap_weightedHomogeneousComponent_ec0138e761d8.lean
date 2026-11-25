-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitCurve_mConeMap_weightedHomogeneousComponent_ec0138e761d8
-- name    : P2M_GroundTheory_Heights__Heights_OrbitCurve_mConeMap_weightedHomogeneousComponent_ec0138e761d8
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:14:05.418126+00:00
-- url     : https://prove2.me/theorems/3cac575d-a8ac-4dfa-8a31-9052461ce999
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Curve m Cone Map weighted Homogeneous Component ec0138e761d8: P2 M Ground Theory Heights  Heights Orbit Curve m Cone Map weighted Homogeneous Component ec0138
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Curve m Cone Map weighted Homogeneous Component ec0138e761d8 construction uses the P2 M Ground Theory Heights  Heights Orbit Curve m Cone Map weighted Homogeneous Component ec0138e761d8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitCurve.lean#L38-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitCurve.lean#L38-L56

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCurve
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G Algebra
noncomputable section
open GroundTheory.Heights₂.Heights.OrbitCurve
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_OrbitCurve_mConeMap_weightedHomogeneousComponent_ec0138e761d8 (x : Cone n (AlgebraicClosure ℚ))
    (f : MvPolynomial (Coord n) ℤ) (b : ι → ℕ) :
    Geo.mConeMap (ι := blockIdx n) (flatCone x) (weightedHomogeneousComponent (coordDeg n) b f) =
      weightedHomogeneousComponent (tDeg ι) b (Geo.mConeMap (ι := blockIdx n) (flatCone x) f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitCurve».«mConeMap_weightedHomogeneousComponent» := P2M_GroundTheory_Heights__Heights_OrbitCurve_mConeMap_weightedHomogeneousComponent_ec0138e761d8
