-- Prove2me | Theorems.Thm_PositivityTheory_HtPt_KtwS_LineTwist_full_of_charts
-- name    : PositivityTheory.HtPt.KtwS.LineTwist.full_of_charts
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:54:05.606618+00:00
-- url     : https://prove2.me/theorems/17d02dc4-6b36-5b93-9c6d-0de7f241d15b
-- title:
--   Line Twist: full of charts
-- statement:
--   The Line Twist construction uses the full of charts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/HodgeTatePoints/FullOfCharts.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/HodgeTatePoints/FullOfCharts.lean#L13-L14

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AssemblyBase
import Definitions.Def_Development_WeilBound_CoreStatements_HodgeTatePoints_ExistsLineBundleTwistMulOf
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PClaimVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleNefPlusAmple
import Definitions.Def_Development_WeilBound_CoreStatements_HodgeTatePoints_FullOfCharts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.HtPt PositivityTheory.HtPt.KtwS
open GroundTheory.Heights₂.Heights.Kleiman
universe u v w

theorem PositivityTheory.HtPt.KtwS.LineTwist.full_of_charts : LineTwist.Statement.{u, w} := by sorry
