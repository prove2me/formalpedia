-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitCurve_isHorizontal_orbitIdeal_fbfadf85b618
-- name    : P2M_GroundTheory_Heights__Heights_OrbitCurve_isHorizontal_orbitIdeal_fbfadf85b618
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T02:27:24.66534+00:00
-- url     : https://prove2.me/theorems/633bfa8c-12cc-5d13-8f44-ea038da1e54d
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Curve is Horizontal orbit Ideal fbfadf85b618: P2 M Ground Theory Heights  Heights Orbit Curve is Horizontal orbit Ideal fbfadf85b618
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Curve is Horizontal orbit Ideal fbfadf85b618 construction uses the P2 M Ground Theory Heights  Heights Orbit Curve is Horizontal orbit Ideal fbfadf85b618 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitCurve.lean#L91-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitCurve.lean#L91-L97

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

theorem P2M_GroundTheory_Heights__Heights_OrbitCurve_isHorizontal_orbitIdeal_fbfadf85b618 (x : Cone n (AlgebraicClosure ℚ)) :
    Geo.IsHorizontal (ι := blockIdx n) (orbitIdeal x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitCurve».«isHorizontal_orbitIdeal» := P2M_GroundTheory_Heights__Heights_OrbitCurve_isHorizontal_orbitIdeal_fbfadf85b618
