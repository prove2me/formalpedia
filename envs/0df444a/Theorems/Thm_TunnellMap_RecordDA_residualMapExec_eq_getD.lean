-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_residualMapExec_eq_getD
-- name    : TunnellMap.RecordDA.residualMapExec_eq_getD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:55:28.442641+00:00
-- url     : https://prove2.me/theorems/ae3d23ac-e598-54fb-83c9-0bd0c608574d
-- title:
--   Record DA: residual Map Exec eq get D
-- statement:
--   The fallback version is the `Option` version with a default.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/FallbackFreeMap.lean#L53-L63
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/FallbackFreeMap.lean#L53-L63

import Definitions.Def_TunnellMap_ComputableFullMap
import Definitions.Def_TunnellMap_FallbackFreeMap
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
open TunnellMap.RecordDA

theorem TunnellMap.RecordDA.residualMapExec_eq_getD (hnpos : 0 < n) (hsq : Squarefree n)
    (fallback : AResidual n) (x : BResidual n) :
    residualMapExec hnpos hsq fallback x =
      (residualMapExecOpt hnpos hsq x).getD fallback := by sorry
