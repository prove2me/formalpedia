-- Prove2me | Theorems.Thm_TunnellMap_conditionalTunnellMap_exactly_two_of_odd_balance
-- name    : TunnellMap.conditionalTunnellMap_exactly_two_of_odd_balance
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:17:03.768819+00:00
-- url     : https://prove2.me/theorems/3a674770-1efd-40e6-8db1-a958ab1da48d
-- title:
--   Tunnell Map: conditional Tunnell Map exactly two of odd balance
-- statement:
--   The two-fiber theorem after the paper's equivalent odd-branch balance
--   hypothesis has been supplied.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrbitLift.lean#L162-L173
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrbitLift.lean#L162-L173

import Definitions.Def_TunnellMap_OrbitRanking
import Definitions.Def_TunnellMap_Assembly
import Definitions.Def_TunnellMap_OrbitLift
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.conditionalTunnellMap_exactly_two_of_odd_balance {n : ℤ}
    (hn : Odd n) (hnpos : 0 < n)
    [Fintype (BOddRep n)] [Fintype (ARep n)]
    (hbalance : Fintype.card (BOddRep n) = Fintype.card (ARep n))
    (a : ARep n) :
    ∃ x₁ x₂,
      x₁ ≠ x₂ ∧
      conditionalTunnellMap (oddEquivOfBalance hn hnpos hbalance) x₁ = a ∧
      conditionalTunnellMap (oddEquivOfBalance hn hnpos hbalance) x₂ = a ∧
      ∀ x, conditionalTunnellMap (oddEquivOfBalance hn hnpos hbalance) x = a ↔
        x = x₁ ∨ x = x₂ := by sorry
