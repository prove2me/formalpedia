-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_run_eq_of_reaches
-- name    : TunnellMap.RecordDA.run_eq_of_reaches
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:20:44.076707+00:00
-- url     : https://prove2.me/theorems/9936ff30-a727-51a7-9552-9d19bdd5d2b0
-- title:
--   Record DA: run eq of reaches
-- statement:
--   **Determinism.**  Any terminating sequence of executable steps from a state
--   ends at exactly the state computed by `run`; in particular every rerun of the
--   machine from the canonical initial state regenerates the same held table, the
--   same records and the same signs.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/InverseByRerun.lean#L157-L162
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/InverseByRerun.lean#L157-L162

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

theorem TunnellMap.RecordDA.run_eq_of_reaches (frames : FrameFamily n) {E E' : DARun n}
    (hreach : Reaches frames E E') (hstop : step frames E' = none) :
    run frames E = E' := by sorry
