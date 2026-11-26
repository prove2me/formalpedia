-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_terminalRunExec_queue_nil
-- name    : TunnellMap.RecordDA.terminalRunExec_queue_nil
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T16:38:19.141872+00:00
-- url     : https://prove2.me/theorems/36fcbad1-c5f1-4cd1-a58c-94fcdaab0f71
-- title:
--   Record DA: terminal Run Exec queue nil
-- statement:
--   **The executable run terminates with an empty queue**, i.e. with every
--   source assigned.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputablePipeline.lean#L127-L133
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputablePipeline.lean#L127-L133

import Definitions.Def_TunnellMap_ComputableRoster
import Definitions.Def_TunnellMap_InverseByRerun
import Definitions.Def_TunnellMap_LagrangeGauss
import Definitions.Def_TunnellMap_DeterministicFrame
import Definitions.Def_TunnellMap_ComputablePipeline
set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen
variable {n : ℤ}
variable [Fintype (BOddRep n)] [Fintype (ARep n)]

theorem TunnellMap.RecordDA.terminalRunExec_queue_nil (hn : Odd n) (hnpos : 0 < n)
    (frames : FrameFamily n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit) :
    (terminalRunExec frames).queue = [] := by sorry
