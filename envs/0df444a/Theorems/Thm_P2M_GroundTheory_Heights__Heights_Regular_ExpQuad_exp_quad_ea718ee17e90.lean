-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_exp_quad_ea718ee17e90
-- name    : P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_exp_quad_ea718ee17e90
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:11.948037+00:00
-- url     : https://prove2.me/theorems/cfb386c6-5c8b-4b85-86b0-a04b428accd4
-- title:
--   P2 M Ground Theory Heights  Heights Regular Exp Quad exp quad ea718ee17e90: P2 M Ground Theory Heights  Heights Regular Exp Quad exp quad ea718ee17e90
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Exp Quad exp quad ea718ee17e90 construction uses the P2 M Ground Theory Heights  Heights Regular Exp Quad exp quad ea718ee17e90 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PExpExtension.lean#L136-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PExpExtension.lean#L136-L143

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StRiemannSlices
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StPuncturedExpOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StLogCoverDescent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PExpExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Filter Topology Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.ExpQuad
variable {n a g : ℕ} (P : PeriodPolydisc n a g) (v : Fin g → ℤ)

theorem P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_exp_quad_ea718ee17e90 (w : Fin n → ℂ) :
    Complex.exp (2 * Real.pi * Complex.I * qf (P.τ w) v) =
      Complex.exp (phi P v w) *
        Complex.exp (∑ i, w (Fin.castLE P.a_le i) * ((intQuad (P.B i) v : ℤ) : ℂ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«ExpQuad».«exp_quad» := P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_exp_quad_ea718ee17e90
