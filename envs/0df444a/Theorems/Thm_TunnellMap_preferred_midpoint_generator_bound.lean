-- Prove2me | Theorems.Thm_TunnellMap_preferred_midpoint_generator_bound
-- name    : TunnellMap.preferred_midpoint_generator_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:27:23.131711+00:00
-- url     : https://prove2.me/theorems/61c1d350-26a2-4b99-bc37-d395c1558571
-- title:
--   Tunnell Map: preferred midpoint generator bound
-- statement:
--   Lemma 4.4 in an integral form: if `d` is the primitive direction of the
--   preferred signed midpoint, then `2 Q(d) ≤ n - 1`.  For odd `n` this is
--   equivalent to `Q(d) ≤ (n-1)/2`.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/MidpointBound.lean#L58-L120
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/MidpointBound.lean#L58-L120

import Definitions.Def_TunnellMap_ProjectiveKey
import Definitions.Def_TunnellMap_MidpointBound
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.preferred_midpoint_generator_bound {n : ℤ} (hn : Odd n)
    (s : BResidual n) (t : AResidual n) :
    2 * qForm (primitiveDirection (preferredVector s t)) ≤ n - 1 := by sorry
