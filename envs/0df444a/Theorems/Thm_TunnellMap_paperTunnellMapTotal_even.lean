-- Prove2me | Theorems.Thm_TunnellMap_paperTunnellMapTotal_even
-- name    : TunnellMap.paperTunnellMapTotal_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:57:57.075576+00:00
-- url     : https://prove2.me/theorems/6b9302ec-5486-516b-8645-17d3e0632e42
-- title:
--   Tunnell Map: paper Tunnell Map Total even
-- statement:
--   **The even branch.**  A source with even third coordinate is halved in
--   that coordinate.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/BranchSpec.lean#L39-L46
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/BranchSpec.lean#L39-L46

import Definitions.Def_TunnellMap_FallbackFreeMap
import Definitions.Def_TunnellMap_BranchSpec
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}

theorem TunnellMap.paperTunnellMapTotal_even (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n) (hbal : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (p : BRep n) (hz : p.1.z % 2 = 0) :
    (paperTunnellMapTotal hn hnpos hsq hbal p).1 =
      ⟨p.1.x, p.1.y, p.1.z / 2⟩ := by sorry
