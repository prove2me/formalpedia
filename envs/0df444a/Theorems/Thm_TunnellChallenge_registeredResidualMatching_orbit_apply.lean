-- Prove2me | Theorems.Thm_TunnellChallenge_registeredResidualMatching_orbit_apply
-- name    : TunnellChallenge.registeredResidualMatching_orbit_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:59:43.163348+00:00
-- url     : https://prove2.me/theorems/eb1e2532-ba17-4df7-80a0-40408b4fb641
-- title:
--   Tunnell Challenge: registered Residual Matching orbit apply
-- statement:
--   The Tunnell Challenge construction uses the registered Residual Matching orbit apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/Solution.lean#L445-L451
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/Solution.lean#L445-L451

import Definitions.Def_TunnellMap_BranchSpec
import Definitions.Def_TunnellMap_Solution
set_option autoImplicit true
open TunnellChallenge
set_option maxHeartbeats 1000000
open Polynomial

theorem TunnellChallenge.registeredResidualMatching_orbit_apply {n : ℤ} (hodd : Odd n)
    (hpos : 0 < n) (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (s : CanonicalB n) :
    canonicalAOrbitEquiv hpos (registeredResidualMatching hodd hpos hbalance s) =
      TunnellMap.residualOrbitMatching hpos
        (coreResidualOrbitCardEq hodd hpos hbalance) (canonicalBOrbitEquiv n s) := by sorry
