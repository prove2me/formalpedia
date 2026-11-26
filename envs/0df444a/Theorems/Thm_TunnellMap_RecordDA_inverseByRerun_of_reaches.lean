-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_inverseByRerun_of_reaches
-- name    : TunnellMap.RecordDA.inverseByRerun_of_reaches
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:34:55.6186+00:00
-- url     : https://prove2.me/theorems/8e1798d8-71c3-42ed-95df-c021acf312d1
-- title:
--   Record DA: inverse By Rerun of reaches
-- statement:
--   **The rerun really is a rerun.**  The record located by `inverseByRerun`
--   is the record held by the state reached by *any* terminating execution of the
--   executable machine from the canonical initial state.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/InverseByRerun.lean#L229-L236
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/InverseByRerun.lean#L229-L236

import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
import Definitions.Def_TunnellMap_RecordSign
import Definitions.Def_TunnellMap_InverseByRerun
set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen GloballyRanked
variable {n : ℤ}
variable [Fintype (BOddRep n)]
variable [Fintype (ARep n)]
omit [Fintype (ARep n)]

theorem TunnellMap.RecordDA.inverseByRerun_of_reaches (frames : FrameFamily n)
    (fallback : BResidual n) (y : AResidual n) {E : DARun n}
    (hreach : Reaches frames (DARun.initial (sourceRoster n)) E)
    (hstop : step frames E = none) :
    inverseByRerun frames fallback y =
      (E.held (canonicalTargetLift (residualTargetLift y))).elim fallback
        fun p => signActB (targetLiftSign (residualTargetLift y) * p.2.sign) p.1 := by sorry
