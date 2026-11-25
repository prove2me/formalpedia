-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_phi_analytic_cb4cbe93b925
-- name    : P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_phi_analytic_cb4cbe93b925
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:07.965171+00:00
-- url     : https://prove2.me/theorems/378ecdbd-6310-482e-b804-24575e12a9bd
-- title:
--   P2 M Ground Theory Heights  Heights Regular Exp Quad phi analytic cb4cbe93b925: P2 M Ground Theory Heights  Heights Regular Exp Quad phi analytic cb4cbe93b925
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Exp Quad phi analytic cb4cbe93b925 construction uses the P2 M Ground Theory Heights  Heights Regular Exp Quad phi analytic cb4cbe93b925 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PExpExtension.lean#L119-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PExpExtension.lean#L119-L130

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

theorem P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_phi_analytic_cb4cbe93b925 : AnalyticOnNhd ℂ (phi P v) (logCover P.a_le) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«ExpQuad».«phi_analytic» := P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_phi_analytic_cb4cbe93b925
