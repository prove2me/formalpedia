-- Prove2me | Theorems.Thm_TunnellMap_some_paperTunnellMapTotal
-- name    : TunnellMap.some_paperTunnellMapTotal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:54:47.103668+00:00
-- url     : https://prove2.me/theorems/64ce88a0-0e04-5e71-b46a-55d98f203233
-- title:
--   Tunnell Map: some paper Tunnell Map Total
-- statement:
--   The Tunnell Map construction uses the some paper Tunnell Map Total property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/FallbackFreeMap.lean#L396-L401
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/FallbackFreeMap.lean#L396-L401

import Definitions.Def_TunnellMap_ComputableFullMap
import Definitions.Def_TunnellMap_FallbackFreeMap
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}

theorem TunnellMap.some_paperTunnellMapTotal (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n) (hbal : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (p : BRep n) :
    some (paperTunnellMapTotal hn hnpos hsq hbal p) =
      paperTunnellMapExecOpt hnpos hsq p := by sorry
