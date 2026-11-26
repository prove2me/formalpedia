-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_sim_terminalRun
-- name    : TunnellMap.RecordDA.sim_terminalRun
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:04:27.918465+00:00
-- url     : https://prove2.me/theorems/bcdd0a16-0fff-4d6d-8001-8f22ac9cf8ea
-- title:
--   Record DA: sim terminal Run
-- statement:
--   The Record DA construction uses the sim terminal Run property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/RecordDeferredAcceptanceCorrect.lean#L817-L819
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/RecordDeferredAcceptanceCorrect.lean#L817-L819

import Definitions.Def_TunnellMap_RecordDeferredAcceptance
import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen GloballyRanked
variable {n : ℤ}
variable [Fintype (BOddRep n)] [Fintype (ARep n)]

theorem TunnellMap.RecordDA.sim_terminalRun (hn : Odd n) (hnpos : 0 < n) (frames : FrameFamily n) :
    Sim hnpos frames (terminalRun frames) := by sorry
