-- Prove2me | Theorems.Thm_TunnellMap_FreeInvolution_card_eq_twice_orbit_card
-- name    : TunnellMap.FreeInvolution.card_eq_twice_orbit_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:42:54.836969+00:00
-- url     : https://prove2.me/theorems/04979686-645a-5ac9-a79c-293a27681822
-- title:
--   Free Involution: card eq twice orbit card
-- statement:
--   The Free Involution construction uses the card eq twice orbit card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Antipodal.lean#L287-L290
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Antipodal.lean#L287-L290

import Definitions.Def_TunnellMap_Midpoint
import Definitions.Def_TunnellMap_Antipodal
set_option autoImplicit true
open TunnellMap
open TunnellMap.FreeInvolution
variable {X : Type*} (I : FreeInvolution X)
variable [Fintype X] [DecidableEq X]

theorem TunnellMap.FreeInvolution.card_eq_twice_orbit_card :
    Fintype.card X = 2 * Fintype.card I.Orbit := by sorry
