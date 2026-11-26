-- Prove2me | Theorems.Thm_TunnellMap_directMapExec_eq
-- name    : TunnellMap.directMapExec_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:13:33.059647+00:00
-- url     : https://prove2.me/theorems/a270d652-6700-4d06-92ff-f012b23b3216
-- title:
--   Tunnell Map: direct Map Exec eq
-- statement:
--   **The computable direct map agrees with the structural equivalence.**
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableDirect.lean#L81-L94
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableDirect.lean#L81-L94

import Definitions.Def_TunnellMap_ResidualBalance
import Definitions.Def_TunnellMap_ComputableRoster
import Definitions.Def_TunnellMap_ComputableDirect
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.directMapExec_eq {n : ℤ} (hn : Odd n) (p : BOddRep n)
    (h : DirectSourceUsed p) :
    directMapExec p = some ((directSubsetEquiv hn ⟨p, h⟩).1) := by sorry
