-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitCurve_ringKrullDim_orbitIdeal_cc019d8891ab
-- name    : P2M_GroundTheory_Heights__Heights_OrbitCurve_ringKrullDim_orbitIdeal_cc019d8891ab
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:13:39.814238+00:00
-- url     : https://prove2.me/theorems/46351d8f-c9dd-40af-8ba2-56b756ce3dfb
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Curve ring Krull Dim orbit Ideal cc019d8891ab: P2 M Ground Theory Heights  Heights Orbit Curve ring Krull Dim orbit Ideal cc019d8891ab
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Curve ring Krull Dim orbit Ideal cc019d8891ab construction uses the P2 M Ground Theory Heights  Heights Orbit Curve ring Krull Dim orbit Ideal cc019d8891ab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitCurve.lean#L179-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitCurve.lean#L179-L188

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

theorem P2M_GroundTheory_Heights__Heights_OrbitCurve_ringKrullDim_orbitIdeal_cc019d8891ab {x : Cone n (AlgebraicClosure ℚ)} (hx : BlockNonzero x) :
    ringKrullDim (MvPolynomial (Coord n) ℤ ⧸ orbitIdeal x) =
      ((1 + Fintype.card ι : ℕ) : WithBot ℕ∞) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitCurve».«ringKrullDim_orbitIdeal» := P2M_GroundTheory_Heights__Heights_OrbitCurve_ringKrullDim_orbitIdeal_cc019d8891ab
