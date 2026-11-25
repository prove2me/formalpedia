-- Prove2me | Theorems.Thm_PositivityTheory_CW_normal_nilpotent_of_commutator
-- name    : PositivityTheory.CW.normal_nilpotent_of_commutator
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:48:18.692555+00:00
-- url     : https://prove2.me/theorems/e42ebaa4-df73-4a27-b9e5-9bb8649c63fa
-- title:
--   CW: normal nilpotent of commutator
-- statement:
--   The CW construction uses the normal nilpotent of commutator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/CommutatorAdjointHolds.lean#L298-L301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/CommutatorAdjointHolds.lean#L298-L301

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_CommutatorAdjointHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS Polynomial
open PositivityTheory PositivityTheory.CW

theorem PositivityTheory.CW.normal_nilpotent_of_commutator : A1 → A2 → A3 → A4 → CommutatorAdjointModLower → A5 := by sorry
