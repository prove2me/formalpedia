-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_heldGenerated_run
-- name    : TunnellMap.RecordDA.heldGenerated_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:20:13.086771+00:00
-- url     : https://prove2.me/theorems/466d451e-6235-5a41-9368-49b063415961
-- title:
--   Record DA: held Generated run
-- statement:
--   The Record DA construction uses the held Generated run property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/InverseByRerun.lean#L96-L109
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/InverseByRerun.lean#L96-L109

import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
import Definitions.Def_TunnellMap_RecordSign
import Definitions.Def_TunnellMap_InverseByRerun
set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen GloballyRanked
variable {n : ℤ}
variable [Fintype (BOddRep n)] [Fintype (ARep n)]

theorem TunnellMap.RecordDA.heldGenerated_run (hn : Odd n) (hnpos : 0 < n) (frames : FrameFamily n) :
    ∀ {E : DARun n}, Sim hnpos frames E → HeldGenerated frames E →
      HeldGenerated frames (run frames E) := by sorry
