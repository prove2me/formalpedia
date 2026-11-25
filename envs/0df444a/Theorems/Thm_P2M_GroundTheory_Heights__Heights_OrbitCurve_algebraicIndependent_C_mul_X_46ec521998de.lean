-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitCurve_algebraicIndependent_C_mul_X_46ec521998de
-- name    : P2M_GroundTheory_Heights__Heights_OrbitCurve_algebraicIndependent_C_mul_X_46ec521998de
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:14:14.335916+00:00
-- url     : https://prove2.me/theorems/4816f77b-0c79-4c98-ae70-9b5fd05b16b5
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Curve algebraic Independent C mul X 46ec521998de: P2 M Ground Theory Heights  Heights Orbit Curve algebraic Independent C mul X 46ec521998de
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Curve algebraic Independent C mul X 46ec521998de construction uses the P2 M Ground Theory Heights  Heights Orbit Curve algebraic Independent C mul X 46ec521998de property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitCurve.lean#L135-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitCurve.lean#L135-L152

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

theorem P2M_GroundTheory_Heights__Heights_OrbitCurve_algebraicIndependent_C_mul_X_46ec521998de (a : ι → AlgebraicClosure ℚ) (ha : ∀ k, a k ≠ 0) :
    AlgebraicIndependent ℚ (fun k ↦ (C (a k) * X k : MvPolynomial ι (AlgebraicClosure ℚ))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitCurve».«algebraicIndependent_C_mul_X» := P2M_GroundTheory_Heights__Heights_OrbitCurve_algebraicIndependent_C_mul_X_46ec521998de
