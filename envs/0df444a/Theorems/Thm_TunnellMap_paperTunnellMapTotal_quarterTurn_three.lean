-- Prove2me | Theorems.Thm_TunnellMap_paperTunnellMapTotal_quarterTurn_three
-- name    : TunnellMap.paperTunnellMapTotal_quarterTurn_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:01:54.095087+00:00
-- url     : https://prove2.me/theorems/1de6f924-5d01-5239-afa6-894bbb7612ec
-- title:
--   Tunnell Map: paper Tunnell Map Total quarter Turn three
-- statement:
--   **The third quarter-turn.**  If the third coordinate is odd, neither of
--   the first two congruences holds and `4 ∣ x`, with quotient `q`, then the image
--   is `(2z, y, -q)`.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/BranchSpec.lean#L91-L106
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/BranchSpec.lean#L91-L106

import Definitions.Def_TunnellMap_FallbackFreeMap
import Definitions.Def_TunnellMap_BranchSpec
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}

theorem TunnellMap.paperTunnellMapTotal_quarterTurn_three (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n) (hbal : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (p : BRep n) (hz : ¬ p.1.z % 2 = 0)
    (h₁ : ¬ (8 : ℤ) ∣ (p.1.x + 2 * p.1.z + p.1.y))
    (h₂ : ¬ (8 : ℤ) ∣ (p.1.y - p.1.x + 2 * p.1.z))
    (h₃ : (4 : ℤ) ∣ p.1.x) :
    (paperTunnellMapTotal hn hnpos hsq hbal p).1 =
      ⟨2 * p.1.z, p.1.y, -(p.1.x / 4)⟩ := by sorry
