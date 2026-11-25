-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitCurve_comap_ker_coneMapQ_3c1fcc541d2a
-- name    : P2M_GroundTheory_Heights__Heights_OrbitCurve_comap_ker_coneMapQ_3c1fcc541d2a
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:13:50.153378+00:00
-- url     : https://prove2.me/theorems/a1fb2f5b-1c25-4eb8-a927-055f72dc0243
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Curve comap ker cone Map Q 3c1fcc541d2a: P2 M Ground Theory Heights  Heights Orbit Curve comap ker cone Map Q 3c1fcc541d2a
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Curve comap ker cone Map Q 3c1fcc541d2a construction uses the P2 M Ground Theory Heights  Heights Orbit Curve comap ker cone Map Q 3c1fcc541d2a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitCurve.lean#L111-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitCurve.lean#L111-L114

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

theorem P2M_GroundTheory_Heights__Heights_OrbitCurve_comap_ker_coneMapQ_3c1fcc541d2a (x : Cone n (AlgebraicClosure ℚ)) :
    (RingHom.ker (coneMapQ x)).comap (map (Int.castRingHom ℚ)) = orbitIdeal x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitCurve».«comap_ker_coneMapQ» := P2M_GroundTheory_Heights__Heights_OrbitCurve_comap_ker_coneMapQ_3c1fcc541d2a
