-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitCurve_weightedHomogeneousComponent_mem_orbitIdeal_da39853aed85
-- name    : P2M_GroundTheory_Heights__Heights_OrbitCurve_weightedHomogeneousComponent_mem_orbitIdeal_da39853aed85
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T02:29:09.487288+00:00
-- url     : https://prove2.me/theorems/16ae62c5-f9b0-48f2-a7b0-cd98f39344b6
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Curve weighted Homogeneous Component mem orbit Ideal da39853aed85: P2 M Ground Theory Heights  Heights Orbit Curve weighted Homogeneous Component mem orbit Id
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Curve weighted Homogeneous Component mem orbit Ideal da39853aed85 construction uses the P2 M Ground Theory Heights  Heights Orbit Curve weighted Homogeneous Component mem orbit Ideal da39853aed85 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitCurve.lean#L65-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitCurve.lean#L65-L69

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

theorem P2M_GroundTheory_Heights__Heights_OrbitCurve_weightedHomogeneousComponent_mem_orbitIdeal_da39853aed85 (x : Cone n (AlgebraicClosure ℚ))
    {f : MvPolynomial (Coord n) ℤ} (hf : f ∈ orbitIdeal x) (b : ι → ℕ) :
    weightedHomogeneousComponent (coordDeg n) b f ∈ orbitIdeal x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitCurve».«weightedHomogeneousComponent_mem_orbitIdeal» := P2M_GroundTheory_Heights__Heights_OrbitCurve_weightedHomogeneousComponent_mem_orbitIdeal_da39853aed85
