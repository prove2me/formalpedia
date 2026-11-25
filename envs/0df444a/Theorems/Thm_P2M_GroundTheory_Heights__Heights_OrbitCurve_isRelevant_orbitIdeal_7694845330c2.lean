-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitCurve_isRelevant_orbitIdeal_7694845330c2
-- name    : P2M_GroundTheory_Heights__Heights_OrbitCurve_isRelevant_orbitIdeal_7694845330c2
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:15:30.834355+00:00
-- url     : https://prove2.me/theorems/37365c29-58d3-4025-9626-565cec8a94ec
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Curve is Relevant orbit Ideal 7694845330c2: P2 M Ground Theory Heights  Heights Orbit Curve is Relevant orbit Ideal 7694845330c2
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Curve is Relevant orbit Ideal 7694845330c2 construction uses the P2 M Ground Theory Heights  Heights Orbit Curve is Relevant orbit Ideal 7694845330c2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitCurve.lean#L82-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitCurve.lean#L82-L87

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

theorem P2M_GroundTheory_Heights__Heights_OrbitCurve_isRelevant_orbitIdeal_7694845330c2 {x : Cone n (AlgebraicClosure ℚ)} (hx : BlockNonzero x) :
    Geo.IsRelevant (ι := blockIdx n) (orbitIdeal x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitCurve».«isRelevant_orbitIdeal» := P2M_GroundTheory_Heights__Heights_OrbitCurve_isRelevant_orbitIdeal_7694845330c2
