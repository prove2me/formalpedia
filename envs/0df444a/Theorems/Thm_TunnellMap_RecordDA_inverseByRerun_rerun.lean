-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_inverseByRerun_rerun
-- name    : TunnellMap.RecordDA.inverseByRerun_rerun
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:10:19.500154+00:00
-- url     : https://prove2.me/theorems/5847815c-bc19-495a-bc93-a7c706b28873
-- title:
--   Record DA: inverse By Rerun rerun
-- statement:
--   The rerun performed by `inverseByRerun` is the canonical integrated run.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/InverseByRerun.lean#L186-L192
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/InverseByRerun.lean#L186-L192

import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
import Definitions.Def_TunnellMap_RecordSign
import Definitions.Def_TunnellMap_InverseByRerun
set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen GloballyRanked
variable {n : ℤ}
variable [Fintype (BOddRep n)]

theorem TunnellMap.RecordDA.inverseByRerun_rerun (frames : FrameFamily n)
    (fallback : BResidual n) (y : AResidual n) :
    inverseByRerun frames fallback y =
      ((terminalRun frames).held
          (canonicalTargetLift (residualTargetLift y))).elim fallback
        fun p => signActB (targetLiftSign (residualTargetLift y) * p.2.sign) p.1 := by sorry
