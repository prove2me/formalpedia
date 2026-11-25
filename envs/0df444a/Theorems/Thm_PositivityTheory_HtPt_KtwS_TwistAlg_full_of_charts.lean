-- Prove2me | Theorems.Thm_PositivityTheory_HtPt_KtwS_TwistAlg_full_of_charts
-- name    : PositivityTheory.HtPt.KtwS.TwistAlg.full_of_charts
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:00:46.463813+00:00
-- url     : https://prove2.me/theorems/640a82de-3513-5c8e-a339-a48968801297
-- title:
--   Twist Alg: full of charts
-- statement:
--   The Twist Alg construction uses the full of charts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/HodgeTatePoints/FullOfCharts.lean#L16-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/HodgeTatePoints/FullOfCharts.lean#L16-L28

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

theorem PositivityTheory.HtPt.KtwS.TwistAlg.full_of_charts : TwistAlg.Statement.{u, w} := by sorry
