-- Prove2me | Theorems.Thm_TunnellMap_paperTunnellMapTotal_quarterTurn_two
-- name    : TunnellMap.paperTunnellMapTotal_quarterTurn_two
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T17:01:28.665216+00:00
-- url     : https://prove2.me/theorems/c00be98a-3ccc-56df-8c29-ba8bc85fa8d9
-- title:
--   Tunnell Map: paper Tunnell Map Total quarter Turn two
-- statement:
--   **The second quarter-turn.**  If the third coordinate is odd,
--   `8 ∤ x + 2z + y` and `8 ∣ y - x + 2z`, with quotient `q`, then the image is
--   `(x - 2z + 4q, -x - 2z, q)`.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/BranchSpec.lean#L71-L86
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/BranchSpec.lean#L71-L86

import Definitions.Def_TunnellMap_FallbackFreeMap
import Definitions.Def_TunnellMap_BranchSpec
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}

theorem TunnellMap.paperTunnellMapTotal_quarterTurn_two (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n) (hbal : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (p : BRep n) (hz : ¬ p.1.z % 2 = 0)
    (h₁ : ¬ (8 : ℤ) ∣ (p.1.x + 2 * p.1.z + p.1.y))
    (h₂ : (8 : ℤ) ∣ (p.1.y - p.1.x + 2 * p.1.z)) :
    (paperTunnellMapTotal hn hnpos hsq hbal p).1 =
      ⟨p.1.x - 2 * p.1.z + 4 * ((p.1.y - p.1.x + 2 * p.1.z) / 8),
        -p.1.x - 2 * p.1.z, (p.1.y - p.1.x + 2 * p.1.z) / 8⟩ := by sorry
