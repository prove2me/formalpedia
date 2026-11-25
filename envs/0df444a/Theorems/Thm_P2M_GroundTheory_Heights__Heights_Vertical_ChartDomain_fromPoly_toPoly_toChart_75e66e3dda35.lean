-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_fromPoly_toPoly_toChart_75e66e3dda35
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_fromPoly_toPoly_toChart_75e66e3dda35
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:42:30.922358+00:00
-- url     : https://prove2.me/theorems/fa2360f3-31a4-4a5f-86c5-777ef294ed90
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Chart Domain from Poly to Poly to Chart 75e66e3dda35: P2 M Ground Theory Heights  Heights Vertical Chart Domain from Poly to Poly to Chart 75e66e3dda35
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Chart Domain from Poly to Poly to Chart 75e66e3dda35 construction uses the P2 M Ground Theory Heights  Heights Vertical Chart Domain from Poly to Poly to Chart 75e66e3dda35 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PChartDomain.lean#L138-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PChartDomain.lean#L138-L161

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChartDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.ChartDomain
variable {D : Type} [CommRing D] {n e : ℕ} (Q : Ideal (MvPolynomial (Fin n) D)) (j : Fin n)

theorem P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_fromPoly_toPoly_toChart_75e66e3dda35 :
    ((fromPoly Q j e).comp (toPoly Q j e)).comp (toChart Q j e) = toChart Q j e := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«ChartDomain».«fromPoly_toPoly_toChart» := P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_fromPoly_toPoly_toChart_75e66e3dda35
