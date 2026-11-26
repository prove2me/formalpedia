-- Prove2me | Theorems.Thm_TunnellMap_paperTunnellMapTotal_eq_exec
-- name    : TunnellMap.paperTunnellMapTotal_eq_exec
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T16:58:07.464737+00:00
-- url     : https://prove2.me/theorems/771800f9-d90a-4200-89f7-b554f58c490d
-- title:
--   Tunnell Map: paper Tunnell Map Total eq exec
-- statement:
--   **The public map agrees with the fallback version** wherever the latter is
--   defined, i.e. for every choice of fallback residual target.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/FallbackFreeMap.lean#L415-L421
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/FallbackFreeMap.lean#L415-L421

import Definitions.Def_TunnellMap_ComputableFullMap
import Definitions.Def_TunnellMap_FallbackFreeMap
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}

theorem TunnellMap.paperTunnellMapTotal_eq_exec (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n) (hbal : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (fallback : AResidual n) (p : BRep n) :
    paperTunnellMapTotal hn hnpos hsq hbal p =
      paperTunnellMapExec hnpos hsq fallback p := by sorry
