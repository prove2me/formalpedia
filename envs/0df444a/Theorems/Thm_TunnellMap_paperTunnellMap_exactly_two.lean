-- Prove2me | Theorems.Thm_TunnellMap_paperTunnellMap_exactly_two
-- name    : TunnellMap.paperTunnellMap_exactly_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:25:51.043303+00:00
-- url     : https://prove2.me/theorems/6351032b-a729-5442-ae1d-4008680dbbe3
-- title:
--   Tunnell Map: paper Tunnell Map exactly two
-- statement:
--   The Tunnell Map construction uses the paper Tunnell Map exactly two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/FullAssembly.lean#L110-L138
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/FullAssembly.lean#L110-L138

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_Finiteness
import Definitions.Def_TunnellMap_FullAssembly
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.paperTunnellMap_exactly_two {n : ℤ} (hn : Odd n) (hnpos : 0 < n)
    [Fintype (BRep n)] [Fintype (ARep n)]
    (hbalance : Fintype.card (BRep n) = 2 * Fintype.card (ARep n))
    (a : ARep n) :
    ∃ p₁ p₂,
      p₁ ≠ p₂ ∧
      paperTunnellMap hn hnpos hbalance p₁ = a ∧
      paperTunnellMap hn hnpos hbalance p₂ = a ∧
      ∀ p, paperTunnellMap hn hnpos hbalance p = a ↔ p = p₁ ∨ p = p₂ := by sorry
