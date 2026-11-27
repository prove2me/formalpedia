-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogDetGramPsh_proof_2e7f61c538dd
-- name    : P2M_GroundTheory_Heights__Heights_LogDetGramPsh_proof_2e7f61c538dd
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:29:34.494868+00:00
-- url     : https://prove2.me/theorems/4321c4b3-f20e-595e-a52e-727865cff8f2
-- title:
--   P2 M Ground Theory Heights  Heights Log Det Gram Psh proof 2e7f61c538dd: P2 M Ground Theory Heights  Heights Log Det Gram Psh proof 2e7f61c538dd
-- statement:
--   The P2 M Ground Theory Heights  Heights Log Det Gram Psh proof 2e7f61c538dd construction uses the P2 M Ground Theory Heights  Heights Log Det Gram Psh proof 2e7f61c538dd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PLogDetGramPsh.lean#L13-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PLogDetGramPsh.lean#L13-L46

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsPsh
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PshMean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PLogDetGramPsh
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
open Matrix Metric Real MCPsh
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_LogDetGramPsh_proof_2e7f61c538dd (hcont : LogDetGramContinuous.Statement)
    (hsub : LogDetGramSubmean.Statement) : LogDetGramPsh.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LogDetGramPsh».«proof» := P2M_GroundTheory_Heights__Heights_LogDetGramPsh_proof_2e7f61c538dd
