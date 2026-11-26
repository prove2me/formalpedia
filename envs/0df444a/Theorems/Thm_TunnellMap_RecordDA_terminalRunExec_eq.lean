-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_terminalRunExec_eq
-- name    : TunnellMap.RecordDA.terminalRunExec_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:06:47.402593+00:00
-- url     : https://prove2.me/theorems/1c86d86a-526b-503b-a797-1e5dc4415fe8
-- title:
--   Record DA: terminal Run Exec eq
-- statement:
--   The Record DA construction uses the terminal Run Exec eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputablePipeline.lean#L103-L105
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputablePipeline.lean#L103-L105

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

theorem TunnellMap.RecordDA.terminalRunExec_eq [Fintype (BOddRep n)] (frames : FrameFamily n) :
    terminalRunExec frames = terminalRun frames := by sorry
