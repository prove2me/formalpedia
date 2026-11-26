-- Prove2me | Theorems.Thm_TunnellMap_paperTunnellMapExec_eq_getD
-- name    : TunnellMap.paperTunnellMapExec_eq_getD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:12:47.382013+00:00
-- url     : https://prove2.me/theorems/6762dac6-fbd6-586c-be25-35c4cd8415f9
-- title:
--   Tunnell Map: paper Tunnell Map Exec eq get D
-- statement:
--   The Tunnell Map construction uses the paper Tunnell Map Exec eq get D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/FallbackFreeMap.lean#L323-L332
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/FallbackFreeMap.lean#L323-L332

import Definitions.Def_TunnellMap_ComputableFullMap
import Definitions.Def_TunnellMap_FallbackFreeMap
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}

theorem TunnellMap.paperTunnellMapExec_eq_getD (hnpos : 0 < n) (hsq : Squarefree n)
    (fallback : AResidual n) (p : BRep n) :
    paperTunnellMapExec hnpos hsq fallback p =
      (paperTunnellMapExecOpt hnpos hsq p).getD fallback.1 := by sorry
