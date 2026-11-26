-- Prove2me | Theorems.Thm_TunnellMap_lifted_first_coordinates_same_parity
-- name    : TunnellMap.lifted_first_coordinates_same_parity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:40:15.256893+00:00
-- url     : https://prove2.me/theorems/5445334a-f6d2-58fb-8e84-d829e3954d25
-- title:
--   Tunnell Map: lifted first coordinates same parity
-- statement:
--   The Tunnell Map construction uses the lifted first coordinates same parity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Midpoint.lean#L52-L85
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Midpoint.lean#L52-L85

import Definitions.Def_TunnellMap_QuarterTurns
import Definitions.Def_TunnellMap_Midpoint
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.lifted_first_coordinates_same_parity {n : ℤ} (hn : Odd n)
    (s : BOddRep n) (t : ARep n) :
    (Even s.1.x ∧ Even t.1.x) ∨ (Odd s.1.x ∧ Odd t.1.x) := by sorry
