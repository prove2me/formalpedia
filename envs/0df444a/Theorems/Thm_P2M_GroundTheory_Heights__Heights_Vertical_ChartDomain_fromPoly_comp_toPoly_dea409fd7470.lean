-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_fromPoly_comp_toPoly_dea409fd7470
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_fromPoly_comp_toPoly_dea409fd7470
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:41:47.211797+00:00
-- url     : https://prove2.me/theorems/76e285f7-f56a-4930-8852-1787d5e7a725
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Chart Domain from Poly comp to Poly dea409fd7470: P2 M Ground Theory Heights  Heights Vertical Chart Domain from Poly comp to Poly dea409fd7470
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Chart Domain from Poly comp to Poly dea409fd7470 construction uses the P2 M Ground Theory Heights  Heights Vertical Chart Domain from Poly comp to Poly dea409fd7470 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PChartDomain.lean#L163-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PChartDomain.lean#L163-L166

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_fromPoly_comp_toPoly_dea409fd7470 : (fromPoly Q j e).comp (toPoly Q j e) = RingHom.id _ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«ChartDomain».«fromPoly_comp_toPoly» := P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_fromPoly_comp_toPoly_dea409fd7470
