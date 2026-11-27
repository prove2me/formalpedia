-- Prove2me | Theorems.Thm_PositivityTheory_ThKEst_FourInj_polish_of_lc
-- name    : PositivityTheory.ThKEst.FourInj.polish_of_lc
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:00:50.46493+00:00
-- url     : https://prove2.me/theorems/f49040e9-6232-4377-afb8-58c095ac6069
-- title:
--   Four Inj: polish of lc
-- statement:
--   The Four Inj construction uses the polish of lc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/FourierInjA.lean#L7-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/FourierInjA.lean#L7-L14

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_FourierInjA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory BoundedContinuousFunction
open PositivityTheory PositivityTheory.ThKEst PositivityTheory.ThKEst.FourInj

theorem PositivityTheory.ThKEst.FourInj.polish_of_lc (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] : PolishSpace G := by sorry
