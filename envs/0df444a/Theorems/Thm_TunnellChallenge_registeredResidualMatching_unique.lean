-- Prove2me | Theorems.Thm_TunnellChallenge_registeredResidualMatching_unique
-- name    : TunnellChallenge.registeredResidualMatching_unique
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T17:02:35.101822+00:00
-- url     : https://prove2.me/theorems/5cccb713-e2de-556a-a990-61d1fc5c681e
-- title:
--   Tunnell Challenge: registered Residual Matching unique
-- statement:
--   The Tunnell Challenge construction uses the registered Residual Matching unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/Solution.lean#L521-L536
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/Solution.lean#L521-L536

import Definitions.Def_TunnellMap_BranchSpec
import Definitions.Def_TunnellMap_Solution
set_option autoImplicit true
open TunnellChallenge
set_option maxHeartbeats 1000000
open Polynomial

theorem TunnellChallenge.registeredResidualMatching_unique {n : ℤ} (hodd : Odd n)
    (hpos : 0 < n) (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (N : CanonicalB n ≃ CanonicalA n) (hN : StableResidualMatching N) :
    N = registeredResidualMatching hodd hpos hbalance := by sorry
