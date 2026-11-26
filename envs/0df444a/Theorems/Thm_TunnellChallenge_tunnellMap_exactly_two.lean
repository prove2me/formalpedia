-- Prove2me | Theorems.Thm_TunnellChallenge_tunnellMap_exactly_two
-- name    : TunnellChallenge.tunnellMap_exactly_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:19:03.945741+00:00
-- url     : https://prove2.me/theorems/2770371b-a50c-425b-9051-f73dc7657b6c
-- title:
--   Tunnell Challenge: tunnell Map exactly two
-- statement:
--   **Every target has exactly two preimages.**
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/Solution.lean#L614-L647
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/Solution.lean#L614-L647

import Definitions.Def_TunnellMap_BranchSpec
import Definitions.Def_TunnellMap_Solution
set_option autoImplicit true
open TunnellChallenge
set_option maxHeartbeats 1000000
open Polynomial

theorem TunnellChallenge.tunnellMap_exactly_two {n : ℤ} (hodd : Odd n) (hpos : 0 < n)
    (hsq : Squarefree n)
    (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (a : ARep n) :
    ∃ p₁ p₂ : BRep n,
      p₁ ≠ p₂ ∧
      tunnellMap hodd hpos hsq hbalance p₁ = a ∧
      tunnellMap hodd hpos hsq hbalance p₂ = a ∧
      ∀ p, tunnellMap hodd hpos hsq hbalance p = a ↔ p = p₁ ∨ p = p₂ := by sorry
