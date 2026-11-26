-- Prove2me | Theorems.Thm_TunnellMap_paperTunnellMapTotal_val_eq
-- name    : TunnellMap.paperTunnellMapTotal_val_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:57:59.209991+00:00
-- url     : https://prove2.me/theorems/abf3e30a-3fea-42f2-a2e2-fad780bcdadf
-- title:
--   Tunnell Map: paper Tunnell Map Total val eq
-- statement:
--   Reading a value off the `Option` computation.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/BranchSpec.lean#L26-L33
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/BranchSpec.lean#L26-L33

import Definitions.Def_TunnellMap_FallbackFreeMap
import Definitions.Def_TunnellMap_BranchSpec
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}

theorem TunnellMap.paperTunnellMapTotal_val_eq (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n) (hbal : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    {p : BRep n} {v : Triple}
    (h : Option.map (fun a : ARep n => a.1) (paperTunnellMapExecOpt hnpos hsq p) =
      some v) :
    (paperTunnellMapTotal hn hnpos hsq hbal p).1 = v := by sorry
