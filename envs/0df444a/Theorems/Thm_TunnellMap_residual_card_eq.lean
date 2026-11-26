-- Prove2me | Theorems.Thm_TunnellMap_residual_card_eq
-- name    : TunnellMap.residual_card_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:46:22.812421+00:00
-- url     : https://prove2.me/theorems/6ce1adac-bb44-5310-b1e3-21f2c2b9b00d
-- title:
--   Tunnell Map: residual card eq
-- statement:
--   The Tunnell Map construction uses the residual card eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ResidualBalance.lean#L210-L221
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ResidualBalance.lean#L210-L221

import Definitions.Def_TunnellMap_Antipodal
import Definitions.Def_TunnellMap_ResidualBalance
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.residual_card_eq {n : ℤ} (hn : Odd n)
    [Fintype (BOddRep n)] [Fintype (ARep n)]
    (hbalance : Fintype.card (BOddRep n) = Fintype.card (ARep n)) :
    Fintype.card (BResidual n) = Fintype.card (AResidual n) := by sorry
