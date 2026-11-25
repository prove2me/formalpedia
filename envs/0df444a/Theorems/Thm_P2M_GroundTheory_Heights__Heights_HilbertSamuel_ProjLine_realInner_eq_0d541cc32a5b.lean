-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_realInner_eq_0d541cc32a5b
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_realInner_eq_0d541cc32a5b
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:21:49.680832+00:00
-- url     : https://prove2.me/theorems/764a8242-d55e-5bc0-b749-76f71daaac92
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Proj Line real Inner eq 0d541cc32a5b: P2 M Ground Theory Heights  Heights Hilbert Samuel Proj Line real Inner eq 0d541cc32a5b
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Proj Line real Inner eq 0d541cc32a5b construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Proj Line real Inner eq 0d541cc32a5b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/ArithModel.lean#L253-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/ArithModel.lean#L253-L255

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsSmoothPts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ArithModel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine
open scoped Topology
variable {J : Type} [Fintype J]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_realInner_eq_0d541cc32a5b (x y : EuclideanSpace ℂ J) : inner ℝ x y = RCLike.re (inner ℂ x y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«ProjLine».«realInner_eq» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_realInner_eq_0d541cc32a5b
