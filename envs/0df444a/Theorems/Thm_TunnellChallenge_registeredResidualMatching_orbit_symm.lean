-- Prove2me | Theorems.Thm_TunnellChallenge_registeredResidualMatching_orbit_symm
-- name    : TunnellChallenge.registeredResidualMatching_orbit_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:59:47.00235+00:00
-- url     : https://prove2.me/theorems/e32d5981-4105-4b82-8d60-66c82e5f5bf2
-- title:
--   Tunnell Challenge: registered Residual Matching orbit symm
-- statement:
--   The Tunnell Challenge construction uses the registered Residual Matching orbit symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/Solution.lean#L453-L460
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/Solution.lean#L453-L460

import Definitions.Def_TunnellMap_BranchSpec
import Definitions.Def_TunnellMap_Solution
set_option autoImplicit true
open TunnellChallenge
set_option maxHeartbeats 1000000
open Polynomial

theorem TunnellChallenge.registeredResidualMatching_orbit_symm {n : ℤ} (hodd : Odd n)
    (hpos : 0 < n) (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (t : CanonicalA n) :
    canonicalBOrbitEquiv n ((registeredResidualMatching hodd hpos hbalance).symm t) =
      (TunnellMap.residualOrbitMatching hpos
        (coreResidualOrbitCardEq hodd hpos hbalance)).symm
          (canonicalAOrbitEquiv hpos t) := by sorry
