-- Prove2me | Theorems.Thm_TunnellMap_paperTunnellMapExec_eq
-- name    : TunnellMap.paperTunnellMapExec_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:13:06.943149+00:00
-- url     : https://prove2.me/theorems/067c4a0d-0f80-502a-aa16-4fc2095b6381
-- title:
--   Tunnell Map: paper Tunnell Map Exec eq
-- statement:
--   **The executable full map agrees with `paperTunnellMap`.**
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableFullMap.lean#L99-L121
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableFullMap.lean#L99-L121

import Definitions.Def_TunnellMap_ComputableDirect
import Definitions.Def_TunnellMap_ComputablePipeline
import Definitions.Def_TunnellMap_FullAssembly
import Definitions.Def_TunnellMap_ComputableFullMap
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
variable [Fintype (BRep n)] [Fintype (ARep n)]

theorem TunnellMap.paperTunnellMapExec_eq (hn : Odd n) (hnpos : 0 < n) (hsq : Squarefree n)
    (hbalance : Fintype.card (BRep n) = 2 * Fintype.card (ARep n))
    (fallback : AResidual n) (p : BRep n) :
    paperTunnellMapExec hnpos hsq fallback p =
      paperTunnellMap hn hnpos hbalance p := by sorry
