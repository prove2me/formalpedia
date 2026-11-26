-- Prove2me | Theorems.Thm_TunnellMap_algorithmicResidualEquiv_inverse_identities
-- name    : TunnellMap.algorithmicResidualEquiv_inverse_identities
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:59:35.797747+00:00
-- url     : https://prove2.me/theorems/0b4ff624-40d0-4199-8e4a-d0f9a97c34d1
-- title:
--   Tunnell Map: algorithmic Residual Equiv inverse identities
-- statement:
--   The regenerated reverse interface is the inverse equivalence; both
--   pointwise inverse identities follow without retaining the proposal history.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ResidualDeferredAcceptance.lean#L216-L223
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ResidualDeferredAcceptance.lean#L216-L223

import Definitions.Def_TunnellMap_OrderedGenerator
import Definitions.Def_TunnellMap_DeferredAcceptanceStability
import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualDeferredAcceptance
set_option autoImplicit true
open TunnellMap
open OrderedGenerator
variable {n : ℤ} (hnpos : 0 < n)
  [Fintype (BOddRep n)] [Fintype (ARep n)]

theorem TunnellMap.algorithmicResidualEquiv_inverse_identities
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit) :
    (∀ s, (algorithmicResidualEquiv hnpos hcard).symm
        (algorithmicResidualEquiv hnpos hcard s) = s) ∧
      (∀ t, algorithmicResidualEquiv hnpos hcard
        ((algorithmicResidualEquiv hnpos hcard).symm t) = t) := by sorry
