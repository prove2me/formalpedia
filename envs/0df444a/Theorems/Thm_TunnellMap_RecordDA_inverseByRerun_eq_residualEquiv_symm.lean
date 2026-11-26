-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_inverseByRerun_eq_residualEquiv_symm
-- name    : TunnellMap.RecordDA.inverseByRerun_eq_residualEquiv_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:20:58.234974+00:00
-- url     : https://prove2.me/theorems/9c55af55-0fa4-543d-b63e-feb47b6246b5
-- title:
--   Record DA: inverse By Rerun eq residual Equiv symm
-- statement:
--   **Agreement with the structural inverse.**  After being defined and
--   verified independently, `inverseByRerun` is extensionally the inverse of the
--   pre-existing residual equivalence.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/InverseByRerun.lean#L303-L313
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/InverseByRerun.lean#L303-L313

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

theorem TunnellMap.RecordDA.inverseByRerun_eq_residualEquiv_symm (hn : Odd n) (hnpos : 0 < n)
    (frames : FrameFamily n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (fallback : BResidual n) (y : AResidual n) :
    inverseByRerun frames fallback y =
      (residualEquivOfOrbitCard hnpos hcard).symm y := by sorry
