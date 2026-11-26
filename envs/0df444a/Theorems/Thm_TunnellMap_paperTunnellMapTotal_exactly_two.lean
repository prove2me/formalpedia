-- Prove2me | Theorems.Thm_TunnellMap_paperTunnellMapTotal_exactly_two
-- name    : TunnellMap.paperTunnellMapTotal_exactly_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:57:59.616257+00:00
-- url     : https://prove2.me/theorems/a930ce4f-c810-410c-a366-1e2653c48e79
-- title:
--   Tunnell Map: paper Tunnell Map Total exactly two
-- statement:
--   **Exactly two preimages, without a fallback.**  Every target
--   representation has exactly two preimages under the public map, under exactly
--   the manuscript hypotheses.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/FallbackFreeMap.lean#L426-L441
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/FallbackFreeMap.lean#L426-L441

import Definitions.Def_TunnellMap_ComputableFullMap
import Definitions.Def_TunnellMap_FallbackFreeMap
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}

theorem TunnellMap.paperTunnellMapTotal_exactly_two (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n) (hbal : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (a : ARep n) :
    ∃ p₁ p₂,
      p₁ ≠ p₂ ∧
      paperTunnellMapTotal hn hnpos hsq hbal p₁ = a ∧
      paperTunnellMapTotal hn hnpos hsq hbal p₂ = a ∧
      ∀ p, paperTunnellMapTotal hn hnpos hsq hbal p = a ↔ p = p₁ ∨ p = p₂ := by sorry
