-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MatrixDetDeriv_hypotheses_met_d0008cb64df5
-- name    : P2M_GroundTheory_Heights__Heights_MatrixDetDeriv_hypotheses_met_d0008cb64df5
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:30:46.985101+00:00
-- url     : https://prove2.me/theorems/23f6561e-edd6-46f0-9dc7-5a57d804f81d
-- title:
--   P2 M Ground Theory Heights  Heights Matrix Det Deriv hypotheses met d0008cb64df5: P2 M Ground Theory Heights  Heights Matrix Det Deriv hypotheses met d0008cb64df5
-- statement:
--   The P2 M Ground Theory Heights  Heights Matrix Det Deriv hypotheses met d0008cb64df5 construction uses the P2 M Ground Theory Heights  Heights Matrix Det Deriv hypotheses met d0008cb64df5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/StatementsBounds.lean#L92-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/StatementsBounds.lean#L92-L98

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_DetIneq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_BoundsY
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Bounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
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
open Matrix
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_MatrixDetDeriv_hypotheses_met_d0008cb64df5 :
    ∀ j l : Fin 2, DifferentiableAt ℝ (fun q : ℝ => (fun _ : ℝ => (1 : Matrix (Fin 2) (Fin 2) ℂ)) q j l) 0 ∧
      ‖(fun _ : ℝ => (1 : Matrix (Fin 2) (Fin 2) ℂ)) 0 j l‖ ≤ 1 ∧
      ‖fderiv ℝ (fun q : ℝ => (fun _ : ℝ => (1 : Matrix (Fin 2) (Fin 2) ℂ)) q j l) 0‖ ≤ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MatrixDetDeriv».«hypotheses_met» := P2M_GroundTheory_Heights__Heights_MatrixDetDeriv_hypotheses_met_d0008cb64df5
