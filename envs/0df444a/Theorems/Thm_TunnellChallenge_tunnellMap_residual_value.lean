-- Prove2me | Theorems.Thm_TunnellChallenge_tunnellMap_residual_value
-- name    : TunnellChallenge.tunnellMap_residual_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:00:51.820613+00:00
-- url     : https://prove2.me/theorems/e9b92505-b3df-5b45-9f98-6faf322075de
-- title:
--   Tunnell Challenge: tunnell Map residual value
-- statement:
--   The Tunnell Challenge construction uses the tunnell Map residual value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/Solution.lean#L723-L758
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/Solution.lean#L723-L758

import Definitions.Def_TunnellMap_BranchSpec
import Definitions.Def_TunnellMap_Solution
set_option autoImplicit true
open TunnellChallenge
set_option maxHeartbeats 1000000
open Polynomial

theorem TunnellChallenge.tunnellMap_residual_value {n : ℤ} (hodd : Odd n) (hpos : 0 < n)
    (hsq : Squarefree n)
    (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (x : BResidual n) :
    aEquiv n (tunnellMap hodd hpos hsq hbalance x.1.1) =
      (TunnellMap.canonicalResidualMapOf hpos
        (TunnellMap.residualOrbitMatching hpos
          (coreResidualOrbitCardEq hodd hpos hbalance)) (brEquiv n x)).1 := by sorry
