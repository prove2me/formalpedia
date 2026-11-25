-- Prove2me | Theorems.Thm_PositivityTheory_CW_second_moment_of_columns
-- name    : PositivityTheory.CW.second_moment_of_columns
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:51:30.613144+00:00
-- url     : https://prove2.me/theorems/be07b770-b612-5dfc-881f-bf4ce5381814
-- title:
--   CW: second moment of columns
-- statement:
--   The CW construction uses the second moment of columns property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/MatrixActionSingle.lean#L66-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/MatrixActionSingle.lean#L66-L207

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_MatrixActionSingle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
set_option maxHeartbeats 800000

theorem PositivityTheory.CW.second_moment_of_columns : A0 → A1 → FiltrationAdjointStable → CasimirIsRealScalar → A5 → A6 → ColumnOperatorMoments → A8 := by sorry
