-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitCurve_ringKrullDim_quot_ker_coneMapQ_a85c2d92f4e2
-- name    : P2M_GroundTheory_Heights__Heights_OrbitCurve_ringKrullDim_quot_ker_coneMapQ_a85c2d92f4e2
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:14:20.131667+00:00
-- url     : https://prove2.me/theorems/e90d7315-527f-4791-97c6-630601cd98d9
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Curve ring Krull Dim quot ker cone Map Q a85c2d92f4e2: P2 M Ground Theory Heights  Heights Orbit Curve ring Krull Dim quot ker cone Map Q a85c2d92f4e2
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Curve ring Krull Dim quot ker cone Map Q a85c2d92f4e2 construction uses the P2 M Ground Theory Heights  Heights Orbit Curve ring Krull Dim quot ker cone Map Q a85c2d92f4e2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitCurve.lean#L171-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitCurve.lean#L171-L177

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

theorem P2M_GroundTheory_Heights__Heights_OrbitCurve_ringKrullDim_quot_ker_coneMapQ_a85c2d92f4e2 {x : Cone n (AlgebraicClosure ℚ)} (hx : BlockNonzero x) :
    ringKrullDim (MvPolynomial (Coord n) ℚ ⧸ RingHom.ker (coneMapQ x)) = Fintype.card ι := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitCurve».«ringKrullDim_quot_ker_coneMapQ» := P2M_GroundTheory_Heights__Heights_OrbitCurve_ringKrullDim_quot_ker_coneMapQ_a85c2d92f4e2
