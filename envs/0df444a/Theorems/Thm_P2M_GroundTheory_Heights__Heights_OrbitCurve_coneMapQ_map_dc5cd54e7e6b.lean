-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitCurve_coneMapQ_map_dc5cd54e7e6b
-- name    : P2M_GroundTheory_Heights__Heights_OrbitCurve_coneMapQ_map_dc5cd54e7e6b
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:14:14.987399+00:00
-- url     : https://prove2.me/theorems/830643c8-f34f-42af-9b5a-a5812a95d737
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Curve cone Map Q map dc5cd54e7e6b: P2 M Ground Theory Heights  Heights Orbit Curve cone Map Q map dc5cd54e7e6b
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Curve cone Map Q map dc5cd54e7e6b construction uses the P2 M Ground Theory Heights  Heights Orbit Curve cone Map Q map dc5cd54e7e6b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitCurve.lean#L104-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitCurve.lean#L104-L107

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
omit [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_OrbitCurve_coneMapQ_map_dc5cd54e7e6b (x : Cone n (AlgebraicClosure ℚ)) (f : MvPolynomial (Coord n) ℤ) :
    coneMapQ x (map (Int.castRingHom ℚ) f) = Geo.mConeMap (ι := blockIdx n) (flatCone x) f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitCurve».«coneMapQ_map» := P2M_GroundTheory_Heights__Heights_OrbitCurve_coneMapQ_map_dc5cd54e7e6b
