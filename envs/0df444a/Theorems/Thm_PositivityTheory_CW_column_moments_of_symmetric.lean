-- Prove2me | Theorems.Thm_PositivityTheory_CW_column_moments_of_symmetric
-- name    : PositivityTheory.CW.column_moments_of_symmetric
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:47:48.891578+00:00
-- url     : https://prove2.me/theorems/0c1b1a7d-4a74-5c2b-9d93-be7e93360193
-- title:
--   CW: column moments of symmetric
-- statement:
--   The CW construction uses the column moments of symmetric property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/ColumnMomentsOfSymmetric.lean#L72-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/ColumnMomentsOfSymmetric.lean#L72-L101

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_ColumnMomentsOfSymmetric
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
open MatrixActionSingle

theorem PositivityTheory.CW.column_moments_of_symmetric : A7 → ColumnOperatorMoments := by sorry
