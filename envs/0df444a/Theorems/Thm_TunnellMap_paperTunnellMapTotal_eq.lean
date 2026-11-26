-- Prove2me | Theorems.Thm_TunnellMap_paperTunnellMapTotal_eq
-- name    : TunnellMap.paperTunnellMapTotal_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:55:31.071204+00:00
-- url     : https://prove2.me/theorems/57ce9906-24d2-587a-bedd-1e734fc1ce5e
-- title:
--   Tunnell Map: paper Tunnell Map Total eq
-- statement:
--   **The public map agrees with `paperTunnellMap`.**
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/FallbackFreeMap.lean#L404-L411
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/FallbackFreeMap.lean#L404-L411

import Definitions.Def_TunnellMap_ComputableFullMap
import Definitions.Def_TunnellMap_FallbackFreeMap
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}

theorem TunnellMap.paperTunnellMapTotal_eq (hn : Odd n) (hnpos : 0 < n) (hsq : Squarefree n)
    (hbal : Nat.card (BRep n) = 2 * Nat.card (ARep n)) (p : BRep n) :
    paperTunnellMapTotal hn hnpos hsq hbal p =
      paperTunnellMap hn hnpos (fintype_balance_of_nat_card hbal) p := by sorry
