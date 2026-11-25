-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCInvEntryBound_inv_diag_bounds_351d6c6385e7
-- name    : P2M_GroundTheory_Heights__Heights_MCInvEntryBound_inv_diag_bounds_351d6c6385e7
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:46:32.683819+00:00
-- url     : https://prove2.me/theorems/3dd81eec-5b3f-5095-9e2d-51d9d4689b64
-- title:
--   P2 M Ground Theory Heights  Heights MCInv Entry Bound inv diag bounds 351d6c6385e7: P2 M Ground Theory Heights  Heights MCInv Entry Bound inv diag bounds 351d6c6385e7
-- statement:
--   The P2 M Ground Theory Heights  Heights MCInv Entry Bound inv diag bounds 351d6c6385e7 construction uses the P2 M Ground Theory Heights  Heights MCInv Entry Bound inv diag bounds 351d6c6385e7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PInvEntryBound.lean#L18-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PInvEntryBound.lean#L18-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PInvEntryBound
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
open GroundTheory.Heights₂.Heights.MCInvEntryBound

theorem P2M_GroundTheory_Heights__Heights_MCInvEntryBound_inv_diag_bounds_351d6c6385e7 {ι : Type*} [Fintype ι] [DecidableEq ι] {Y : Matrix ι ι ℝ} {c : ℝ}
    (hc : 0 < c) (h : (Y - c • (1 : Matrix ι ι ℝ)).PosSemidef) (j : ι) :
    0 ≤ Y⁻¹ j j ∧ Y⁻¹ j j ≤ c⁻¹ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCInvEntryBound».«inv_diag_bounds» := P2M_GroundTheory_Heights__Heights_MCInvEntryBound_inv_diag_bounds_351d6c6385e7
