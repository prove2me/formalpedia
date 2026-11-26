-- Prove2me | Theorems.Thm_TunnellChallenge_registeredResidualMatching_target_rep
-- name    : TunnellChallenge.registeredResidualMatching_target_rep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:59:38.446488+00:00
-- url     : https://prove2.me/theorems/950f16fb-8448-49fa-96eb-6765a4134526
-- title:
--   Tunnell Challenge: registered Residual Matching target rep
-- statement:
--   The Tunnell Challenge construction uses the registered Residual Matching target rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/Solution.lean#L462-L471
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/Solution.lean#L462-L471

import Definitions.Def_TunnellMap_BranchSpec
import Definitions.Def_TunnellMap_Solution
set_option autoImplicit true
open TunnellChallenge
set_option maxHeartbeats 1000000
open Polynomial

theorem TunnellChallenge.registeredResidualMatching_target_rep {n : ℤ} (hodd : Odd n)
    (hpos : 0 < n) (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (s : CanonicalB n) :
    arEquiv n (registeredResidualMatching hodd hpos hbalance s).1 =
      TunnellMap.canonicalAResidualRepresentative hpos
        (TunnellMap.residualOrbitMatching hpos
          (coreResidualOrbitCardEq hodd hpos hbalance)
            ((TunnellMap.bResidualInvolution n).orbit (brEquiv n s.1))) := by sorry
