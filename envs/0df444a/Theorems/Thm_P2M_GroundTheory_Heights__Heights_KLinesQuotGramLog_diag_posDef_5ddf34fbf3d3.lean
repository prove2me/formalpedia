-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesQuotGramLog_diag_posDef_5ddf34fbf3d3
-- name    : P2M_GroundTheory_Heights__Heights_KLinesQuotGramLog_diag_posDef_5ddf34fbf3d3
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:26:28.587825+00:00
-- url     : https://prove2.me/theorems/f7bb73aa-9430-4e0d-92b6-9cf389e4f3a0
-- title:
--   P2 M Ground Theory Heights  Heights KLines Quot Gram Log diag pos Def 5ddf34fbf3d3: P2 M Ground Theory Heights  Heights KLines Quot Gram Log diag pos Def 5ddf34fbf3d3
-- statement:
--   The P2 M Ground Theory Heights  Heights KLines Quot Gram Log diag pos Def 5ddf34fbf3d3 construction uses the P2 M Ground Theory Heights  Heights KLines Quot Gram Log diag pos Def 5ddf34fbf3d3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesQuotGramLog.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesQuotGramLog.lean#L21-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesQuotGramLog
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
open scoped ComplexOrder
open GroundTheory.Heights₂.Heights.KLinesQuotGramLog

theorem P2M_GroundTheory_Heights__Heights_KLinesQuotGramLog_diag_posDef_5ddf34fbf3d3 {n : ℕ} (d : Fin n → ℝ) (hd : ∀ x, 0 < d x) :
    (Matrix.diagonal fun x => (d x : ℂ)).PosDef := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KLinesQuotGramLog».«diag_posDef» := P2M_GroundTheory_Heights__Heights_KLinesQuotGramLog_diag_posDef_5ddf34fbf3d3
