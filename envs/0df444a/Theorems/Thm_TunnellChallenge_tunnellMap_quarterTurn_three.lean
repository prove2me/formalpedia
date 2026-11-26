-- Prove2me | Theorems.Thm_TunnellChallenge_tunnellMap_quarterTurn_three
-- name    : TunnellChallenge.tunnellMap_quarterTurn_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:19:42.528282+00:00
-- url     : https://prove2.me/theorems/ef3c37a6-fe8e-494b-8746-bfbe137e91ea
-- title:
--   Tunnell Challenge: tunnell Map quarter Turn three
-- statement:
--   **The third quarter-turn.**
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/Solution.lean#L692-L703
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/Solution.lean#L692-L703

import Definitions.Def_TunnellMap_BranchSpec
import Definitions.Def_TunnellMap_Solution
set_option autoImplicit true
open TunnellChallenge
set_option maxHeartbeats 1000000
open Polynomial

theorem TunnellChallenge.tunnellMap_quarterTurn_three {n : ℤ} (hodd : Odd n) (hpos : 0 < n)
    (hsq : Squarefree n)
    (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (p : BRep n) (hz : ¬ p.1.2.2 % 2 = 0)
    (h₁ : ¬ (8 : ℤ) ∣ (p.1.1 + 2 * p.1.2.2 + p.1.2.1))
    (h₂ : ¬ (8 : ℤ) ∣ (p.1.2.1 - p.1.1 + 2 * p.1.2.2))
    (h₃ : (4 : ℤ) ∣ p.1.1) :
    (tunnellMap hodd hpos hsq hbalance p).1 =
      (2 * p.1.2.2, p.1.2.1, -(p.1.1 / 4)) := by sorry
