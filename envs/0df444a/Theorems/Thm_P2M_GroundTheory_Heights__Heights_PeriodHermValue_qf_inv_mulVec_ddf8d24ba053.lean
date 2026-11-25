-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PeriodHermValue_qf_inv_mulVec_ddf8d24ba053
-- name    : P2M_GroundTheory_Heights__Heights_PeriodHermValue_qf_inv_mulVec_ddf8d24ba053
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:14:21.4556+00:00
-- url     : https://prove2.me/theorems/f2c4c1af-d339-4a9b-b02b-eb3d703a6237
-- title:
--   P2 M Ground Theory Heights  Heights Period Herm Value qf inv mul Vec ddf8d24ba053: P2 M Ground Theory Heights  Heights Period Herm Value qf inv mul Vec ddf8d24ba053
-- statement:
--   The P2 M Ground Theory Heights  Heights Period Herm Value qf inv mul Vec ddf8d24ba053 construction uses the P2 M Ground Theory Heights  Heights Period Herm Value qf inv mul Vec ddf8d24ba053 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PPeriodHermValue.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PPeriodHermValue.lean#L27-L30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PPeriodHermValue
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
open GroundTheory.Heights₂.Heights.PeriodHermValue

theorem P2M_GroundTheory_Heights__Heights_PeriodHermValue_qf_inv_mulVec_ddf8d24ba053 {g : ℕ} (Y : Matrix (Fin g) (Fin g) ℝ) (hY : IsUnit Y.det)
    (β : Fin g → ℝ) : MCSchur.qf Y⁻¹ (Y *ᵥ β) = MCSchur.qf Y β := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PeriodHermValue».«qf_inv_mulVec» := P2M_GroundTheory_Heights__Heights_PeriodHermValue_qf_inv_mulVec_ddf8d24ba053
