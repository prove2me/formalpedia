-- Prove2me | Theorems.Thm_PositivityTheory_CW_maxPr_of
-- name    : PositivityTheory.CW.maxPr_of
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:47:46.462077+00:00
-- url     : https://prove2.me/theorems/2b2ffdbc-9cd6-4104-b64c-f2e31f2c532d
-- title:
--   CW: max Pr of
-- statement:
--   The CW construction uses the max Pr of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/PMaxPr.lean#L28-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/PMaxPr.lean#L28-L84

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_PMaxPr
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
open PMaxPr

theorem PositivityTheory.CW.maxPr_of : CasimirIsRealScalar → EigenbasisExists → A13 → UnitaryGroupFacts → MaximumPrincipleVar → SumSquaresSecondDerivative → B5 → MaxPr := by sorry
