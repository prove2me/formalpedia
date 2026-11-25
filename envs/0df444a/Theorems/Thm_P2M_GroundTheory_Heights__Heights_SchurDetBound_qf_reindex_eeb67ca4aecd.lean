-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SchurDetBound_qf_reindex_eeb67ca4aecd
-- name    : P2M_GroundTheory_Heights__Heights_SchurDetBound_qf_reindex_eeb67ca4aecd
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:36:49.814105+00:00
-- url     : https://prove2.me/theorems/89c6b4d6-c80b-4d83-bc9b-2a7c0a1aa384
-- title:
--   P2 M Ground Theory Heights  Heights Schur Det Bound qf reindex eeb67ca4aecd: P2 M Ground Theory Heights  Heights Schur Det Bound qf reindex eeb67ca4aecd
-- statement:
--   The P2 M Ground Theory Heights  Heights Schur Det Bound qf reindex eeb67ca4aecd construction uses the P2 M Ground Theory Heights  Heights Schur Det Bound qf reindex eeb67ca4aecd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PSchurDetBound.lean#L15-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PSchurDetBound.lean#L15-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PSchurDetBound
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
open GroundTheory.Heights₂.Heights.SchurDetBound

theorem P2M_GroundTheory_Heights__Heights_SchurDetBound_qf_reindex_eeb67ca4aecd {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (G : Matrix ι ι ℝ)
    (w : κ → ℝ) : MCSchur.qf G (w ∘ e) = MCSchur.qf (reindex e e G) w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SchurDetBound».«qf_reindex» := P2M_GroundTheory_Heights__Heights_SchurDetBound_qf_reindex_eeb67ca4aecd
