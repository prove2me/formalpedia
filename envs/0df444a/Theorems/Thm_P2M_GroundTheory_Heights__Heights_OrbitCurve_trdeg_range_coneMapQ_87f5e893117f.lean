-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitCurve_trdeg_range_coneMapQ_87f5e893117f
-- name    : P2M_GroundTheory_Heights__Heights_OrbitCurve_trdeg_range_coneMapQ_87f5e893117f
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:13:39.844186+00:00
-- url     : https://prove2.me/theorems/c9fe4914-3148-4b4c-98a6-bf3002624f8e
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Curve trdeg range cone Map Q 87f5e893117f: P2 M Ground Theory Heights  Heights Orbit Curve trdeg range cone Map Q 87f5e893117f
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Curve trdeg range cone Map Q 87f5e893117f construction uses the P2 M Ground Theory Heights  Heights Orbit Curve trdeg range cone Map Q 87f5e893117f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitCurve.lean#L154-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitCurve.lean#L154-L169

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

theorem P2M_GroundTheory_Heights__Heights_OrbitCurve_trdeg_range_coneMapQ_87f5e893117f {x : Cone n (AlgebraicClosure ℚ)} (hx : BlockNonzero x) :
    trdeg ℚ (coneMapQ x).range = Fintype.card ι := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitCurve».«trdeg_range_coneMapQ» := P2M_GroundTheory_Heights__Heights_OrbitCurve_trdeg_range_coneMapQ_87f5e893117f
