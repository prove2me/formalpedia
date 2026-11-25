-- Prove2me | Theorems.Thm_PositivityTheory_CW_maximum_principle_of_facts
-- name    : PositivityTheory.CW.maximum_principle_of_facts
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:49:06.096651+00:00
-- url     : https://prove2.me/theorems/f471ca32-fff7-4f46-b173-db40af0186fd
-- title:
--   CW: maximum principle of facts
-- statement:
--   The CW construction uses the maximum principle of facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/MaximumPrincipleOfFacts.lean#L51-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/MaximumPrincipleOfFacts.lean#L51-L129

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_MaximumPrincipleOfFacts
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
open MaximumPrincipleOneFunction

theorem PositivityTheory.CW.maximum_principle_of_facts : B2 → B3 → UnitaryGroupFacts → MaximumPrincipleVar := by sorry
