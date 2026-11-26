-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_inverseByRerunExec_eq
-- name    : TunnellMap.RecordDA.inverseByRerunExec_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:08:00.872907+00:00
-- url     : https://prove2.me/theorems/e3905424-9b86-457f-a8df-1f91e14ab80a
-- title:
--   Record DA: inverse By Rerun Exec eq
-- statement:
--   **Agreement of the executable inverse with `inverseByRerun`.**
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputablePipeline.lean#L262-L266
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputablePipeline.lean#L262-L266

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
variable [Fintype (BOddRep n)]

theorem TunnellMap.RecordDA.inverseByRerunExec_eq (hsq : Squarefree n) (fallback : BResidual n)
    (y : AResidual n) :
    inverseByRerunExec hsq fallback y =
      inverseByRerun (framesExec hsq) fallback y := by sorry
