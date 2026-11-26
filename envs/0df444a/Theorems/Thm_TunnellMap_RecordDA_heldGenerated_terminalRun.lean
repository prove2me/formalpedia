-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_heldGenerated_terminalRun
-- name    : TunnellMap.RecordDA.heldGenerated_terminalRun
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:20:45.184394+00:00
-- url     : https://prove2.me/theorems/eae1d1de-592c-5a8a-b750-27b603f03a5e
-- title:
--   Record DA: held Generated terminal Run
-- statement:
--   The Record DA construction uses the held Generated terminal Run property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/InverseByRerun.lean#L111-L114
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/InverseByRerun.lean#L111-L114

import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
import Definitions.Def_TunnellMap_RecordSign
import Definitions.Def_TunnellMap_InverseByRerun
set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen GloballyRanked
variable {n : ℤ}
variable [Fintype (BOddRep n)] [Fintype (ARep n)]

theorem TunnellMap.RecordDA.heldGenerated_terminalRun (hn : Odd n) (hnpos : 0 < n)
    (frames : FrameFamily n) : HeldGenerated frames (terminalRun frames) := by sorry
