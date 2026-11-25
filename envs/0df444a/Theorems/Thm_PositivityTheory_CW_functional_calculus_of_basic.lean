-- Prove2me | Theorems.Thm_PositivityTheory_CW_functional_calculus_of_basic
-- name    : PositivityTheory.CW.functional_calculus_of_basic
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:47:52.743801+00:00
-- url     : https://prove2.me/theorems/f9a69b04-f06c-46bb-b7a5-4938f981e366
-- title:
--   CW: functional calculus of basic
-- statement:
--   The CW construction uses the functional calculus of basic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/FunctionalCalculusOfBasic.lean#L71-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/FunctionalCalculusOfBasic.lean#L71-L104

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusOfBasic
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
open FunctionalCalculusInner

theorem PositivityTheory.CW.functional_calculus_of_basic : A0 → FunctionalCalculusLaws := by sorry
