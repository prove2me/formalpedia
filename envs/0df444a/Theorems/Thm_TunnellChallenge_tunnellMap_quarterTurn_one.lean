-- Prove2me | Theorems.Thm_TunnellChallenge_tunnellMap_quarterTurn_one
-- name    : TunnellChallenge.tunnellMap_quarterTurn_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:19:33.576041+00:00
-- url     : https://prove2.me/theorems/9d932c48-71f0-4203-b33a-228cbad2351d
-- title:
--   Tunnell Challenge: tunnell Map quarter Turn one
-- statement:
--   **The first quarter-turn.**
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/Solution.lean#L663-L674
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/Solution.lean#L663-L674

import Definitions.Def_TunnellMap_BranchSpec
import Definitions.Def_TunnellMap_Solution
set_option autoImplicit true
open TunnellChallenge
set_option maxHeartbeats 1000000
open Polynomial

theorem TunnellChallenge.tunnellMap_quarterTurn_one {n : ℤ} (hodd : Odd n) (hpos : 0 < n)
    (hsq : Squarefree n)
    (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (p : BRep n) (hz : ¬ p.1.2.2 % 2 = 0)
    (h₁ : (8 : ℤ) ∣ (p.1.1 + 2 * p.1.2.2 + p.1.2.1)) :
    (tunnellMap hodd hpos hsq hbalance p).1 =
      (4 * ((p.1.1 + 2 * p.1.2.2 + p.1.2.1) / 8) - p.1.2.1,
        p.1.1 - 2 * p.1.2.2,
        (p.1.1 + 2 * p.1.2.2 + p.1.2.1) / 8) := by sorry
