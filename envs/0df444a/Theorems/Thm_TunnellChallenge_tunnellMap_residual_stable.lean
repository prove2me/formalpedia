-- Prove2me | Theorems.Thm_TunnellChallenge_tunnellMap_residual_stable
-- name    : TunnellChallenge.tunnellMap_residual_stable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:19:38.661542+00:00
-- url     : https://prove2.me/theorems/4e52fe79-b1b9-5cd0-8147-bfde32f75dce
-- title:
--   Tunnell Challenge: tunnell Map residual stable
-- statement:
--   **The residual branch is the projectively ranked stable perfect
--   equivalence with its canonical sign lift.**
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/Solution.lean#L774-L830
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/Solution.lean#L774-L830

import Definitions.Def_TunnellMap_BranchSpec
import Definitions.Def_TunnellMap_Solution
set_option autoImplicit true
open TunnellChallenge
set_option maxHeartbeats 1000000
open Polynomial

theorem TunnellChallenge.tunnellMap_residual_stable {n : ℤ} (hodd : Odd n) (hpos : 0 < n)
    (hsq : Squarefree n)
    (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n)) :
    ∃ M : CanonicalB n ≃ CanonicalA n,
      StableResidualMatching M ∧
        (∀ N : CanonicalB n ≃ CanonicalA n,
          StableResidualMatching N → N = M) ∧
        ∀ s : CanonicalB n,
          tunnellMap hodd hpos hsq hbalance s.1.1.1 =
              (preferredTarget s.1 (M s).1).1 ∧
            tunnellMap hodd hpos hsq hbalance (negBResidual s.1).1.1 =
              (preferredTarget (negBResidual s.1) (M s).1).1 := by sorry
