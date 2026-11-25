-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitCurve_ker_coneMapQ_0aa641207f8f
-- name    : P2M_GroundTheory_Heights__Heights_OrbitCurve_ker_coneMapQ_0aa641207f8f
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T02:02:01.447788+00:00
-- url     : https://prove2.me/theorems/d5dfb950-9e6b-5a24-8a44-03a5f9cf95e9
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Curve ker cone Map Q 0aa641207f8f: P2 M Ground Theory Heights  Heights Orbit Curve ker cone Map Q 0aa641207f8f
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Curve ker cone Map Q 0aa641207f8f construction uses the P2 M Ground Theory Heights  Heights Orbit Curve ker cone Map Q 0aa641207f8f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitCurve.lean#L118-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitCurve.lean#L118-L131

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
omit [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_OrbitCurve_ker_coneMapQ_0aa641207f8f (x : Cone n (AlgebraicClosure ℚ)) :
    RingHom.ker (coneMapQ x) = ReciprocityTheory.AnForm.R.extQ (orbitIdeal x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitCurve».«ker_coneMapQ» := P2M_GroundTheory_Heights__Heights_OrbitCurve_ker_coneMapQ_0aa641207f8f
