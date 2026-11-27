-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PivotBounds_proof_90bf0289c2f7
-- name    : P2M_GroundTheory_Heights__Heights_PivotBounds_proof_90bf0289c2f7
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:34:17.301507+00:00
-- url     : https://prove2.me/theorems/cf35be39-c119-490c-b8e7-7a8e67a97424
-- title:
--   P2 M Ground Theory Heights  Heights Pivot Bounds proof 90bf0289c2f7: P2 M Ground Theory Heights  Heights Pivot Bounds proof 90bf0289c2f7
-- statement:
--   The P2 M Ground Theory Heights  Heights Pivot Bounds proof 90bf0289c2f7 construction uses the P2 M Ground Theory Heights  Heights Pivot Bounds proof 90bf0289c2f7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PPivotBounds.lean#L39-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PPivotBounds.lean#L39-L76

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PPivotBounds
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

theorem P2M_GroundTheory_Heights__Heights_PivotBounds_proof_90bf0289c2f7 (hLL : LeadMinorLeading.Statement) (hLB : LeadMinorBasic.Statement)
    (hPI : PivotInvDiag.Statement) (hPL : PivotLast.Statement) : PivotBounds.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PivotBounds».«proof» := P2M_GroundTheory_Heights__Heights_PivotBounds_proof_90bf0289c2f7
