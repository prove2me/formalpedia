-- Prove2me | Theorems.Thm_TunnellMap_paperTunnellMapExec_exactly_two
-- name    : TunnellMap.paperTunnellMapExec_exactly_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:26:31.658494+00:00
-- url     : https://prove2.me/theorems/471e5ab7-3dc2-4e9f-8945-57840c673518
-- title:
--   Tunnell Map: paper Tunnell Map Exec exactly two
-- statement:
--   **Exactly two preimages.**  Every target representation has exactly two
--   preimages under the executable full map.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableFullMap.lean#L125-L141
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableFullMap.lean#L125-L141

import Definitions.Def_TunnellMap_ComputableDirect
import Definitions.Def_TunnellMap_ComputablePipeline
import Definitions.Def_TunnellMap_FullAssembly
import Definitions.Def_TunnellMap_ComputableFullMap
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
variable [Fintype (BRep n)] [Fintype (ARep n)]

theorem TunnellMap.paperTunnellMapExec_exactly_two (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n)
    (hbalance : Fintype.card (BRep n) = 2 * Fintype.card (ARep n))
    (fallback : AResidual n) (a : ARep n) :
    ∃ p₁ p₂,
      p₁ ≠ p₂ ∧
      paperTunnellMapExec hnpos hsq fallback p₁ = a ∧
      paperTunnellMapExec hnpos hsq fallback p₂ = a ∧
      ∀ p, paperTunnellMapExec hnpos hsq fallback p = a ↔ p = p₁ ∨ p = p₂ := by sorry
