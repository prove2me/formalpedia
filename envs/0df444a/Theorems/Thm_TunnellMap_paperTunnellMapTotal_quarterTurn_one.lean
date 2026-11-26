-- Prove2me | Theorems.Thm_TunnellMap_paperTunnellMapTotal_quarterTurn_one
-- name    : TunnellMap.paperTunnellMapTotal_quarterTurn_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T16:58:17.091826+00:00
-- url     : https://prove2.me/theorems/f800262d-9413-5b77-99b0-07bd4923f38f
-- title:
--   Tunnell Map: paper Tunnell Map Total quarter Turn one
-- statement:
--   **The first quarter-turn.**  If the third coordinate is odd and
--   `8 ∣ x + 2z + y`, with quotient `q`, then the image is `(4q - y, x - 2z, q)`.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/BranchSpec.lean#L52-L66
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/BranchSpec.lean#L52-L66

import Definitions.Def_TunnellMap_FallbackFreeMap
import Definitions.Def_TunnellMap_BranchSpec
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}

theorem TunnellMap.paperTunnellMapTotal_quarterTurn_one (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n) (hbal : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (p : BRep n) (hz : ¬ p.1.z % 2 = 0)
    (h₁ : (8 : ℤ) ∣ (p.1.x + 2 * p.1.z + p.1.y)) :
    (paperTunnellMapTotal hn hnpos hsq hbal p).1 =
      ⟨4 * ((p.1.x + 2 * p.1.z + p.1.y) / 8) - p.1.y, p.1.x - 2 * p.1.z,
        (p.1.x + 2 * p.1.z + p.1.y) / 8⟩ := by sorry
