-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCInvEntryDeriv_differentiableAt_det_6cbb36123359
-- name    : P2M_GroundTheory_Heights__Heights_MCInvEntryDeriv_differentiableAt_det_6cbb36123359
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:35:16.194414+00:00
-- url     : https://prove2.me/theorems/ecc50e0b-785a-4103-827f-a1ac462fb3a7
-- title:
--   P2 M Ground Theory Heights  Heights MCInv Entry Deriv differentiable At det 6cbb36123359: P2 M Ground Theory Heights  Heights MCInv Entry Deriv differentiable At det 6cbb36123359
-- statement:
--   The P2 M Ground Theory Heights  Heights MCInv Entry Deriv differentiable At det 6cbb36123359 construction uses the P2 M Ground Theory Heights  Heights MCInv Entry Deriv differentiable At det 6cbb36123359 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PInvEntryDeriv.lean#L14-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PInvEntryDeriv.lean#L14-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PInvEntryDeriv
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
open Matrix Topology
open GroundTheory.Heights₂.Heights.MCInvEntryDeriv
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : ℕ}

theorem P2M_GroundTheory_Heights__Heights_MCInvEntryDeriv_differentiableAt_det_6cbb36123359 {M : E → Matrix (Fin g) (Fin g) ℝ} {p : E}
    (hM : ∀ j l, DifferentiableAt ℝ (fun q => M q j l) p) :
    DifferentiableAt ℝ (fun q => (M q).det) p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCInvEntryDeriv».«differentiableAt_det» := P2M_GroundTheory_Heights__Heights_MCInvEntryDeriv_differentiableAt_det_6cbb36123359
