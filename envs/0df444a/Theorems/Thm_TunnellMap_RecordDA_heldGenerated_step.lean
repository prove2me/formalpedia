-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_heldGenerated_step
-- name    : TunnellMap.RecordDA.heldGenerated_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:19:59.43103+00:00
-- url     : https://prove2.me/theorems/c0b5cf86-a1a7-5185-87ac-5fb1a32ad319
-- title:
--   Record DA: held Generated step
-- statement:
--   The Record DA construction uses the held Generated step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/InverseByRerun.lean#L55-L94
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/InverseByRerun.lean#L55-L94

import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
import Definitions.Def_TunnellMap_RecordSign
import Definitions.Def_TunnellMap_InverseByRerun
set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen GloballyRanked
variable {n : ℤ}
variable [Fintype (BOddRep n)] [Fintype (ARep n)]
omit [Fintype (BOddRep n)] [Fintype (ARep n)]

theorem TunnellMap.RecordDA.heldGenerated_step (hnpos : 0 < n) (frames : FrameFamily n)
    {E E' : DARun n} (hSim : Sim hnpos frames E)
    (hHG : HeldGenerated frames E) (h : step frames E = some E') :
    HeldGenerated frames E' := by sorry
