-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_toPoly_toChart_090ab285bd50
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_toPoly_toChart_090ab285bd50
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:01:19.465417+00:00
-- url     : https://prove2.me/theorems/4cd6ac27-582f-402e-8c36-4ce4029634bb
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Chart Domain to Poly to Chart 090ab285bd50: P2 M Ground Theory Heights  Heights Vertical Chart Domain to Poly to Chart 090ab285bd50
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Chart Domain to Poly to Chart 090ab285bd50 construction uses the P2 M Ground Theory Heights  Heights Vertical Chart Domain to Poly to Chart 090ab285bd50 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PChartDomain.lean#L93-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PChartDomain.lean#L93-L95

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_toPoly_toChart_090ab285bd50 (e : ℕ) (a : MvPolynomial (Fin n) (MvPolynomial (Par e n) D)) :
    toPoly Q j e (toChart Q j e a) = evalF Q j e a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«ChartDomain».«toPoly_toChart» := P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_toPoly_toChart_090ab285bd50
