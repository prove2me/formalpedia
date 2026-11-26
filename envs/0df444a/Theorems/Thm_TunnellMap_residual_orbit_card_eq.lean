-- Prove2me | Theorems.Thm_TunnellMap_residual_orbit_card_eq
-- name    : TunnellMap.residual_orbit_card_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:50:12.180965+00:00
-- url     : https://prove2.me/theorems/f199a3e1-6c93-4349-8b1b-f1d385dab8ce
-- title:
--   Tunnell Map: residual orbit card eq
-- statement:
--   The Tunnell Map construction uses the residual orbit card eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ResidualBalance.lean#L223-L237
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ResidualBalance.lean#L223-L237

import Definitions.Def_TunnellMap_Antipodal
import Definitions.Def_TunnellMap_ResidualBalance
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.residual_orbit_card_eq {n : ℤ} (hn : Odd n) (hnpos : 0 < n)
    [Fintype (BOddRep n)] [Fintype (ARep n)]
    (hbalance : Fintype.card (BOddRep n) = Fintype.card (ARep n)) :
    Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit := by sorry
