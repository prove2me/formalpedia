-- Prove2me | Theorems.Thm_TunnellMap_OrderedGenerator_q_mem_search_bounds
-- name    : TunnellMap.OrderedGenerator.q_mem_search_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:51:50.648151+00:00
-- url     : https://prove2.me/theorems/20eec25c-04ae-52a6-9dde-b90c9b54c2d0
-- title:
--   Ordered Generator: q mem search bounds
-- statement:
--   The Ordered Generator construction uses the q mem search bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrderedGenerator.lean#L186-L196
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrderedGenerator.lean#L186-L196

import Definitions.Def_TunnellMap_GeneratorSoundness
import Definitions.Def_TunnellMap_OrbitRanking
import Definitions.Def_TunnellMap_PreferenceList
import Definitions.Def_TunnellMap_OrderedGenerator
set_option autoImplicit true
open TunnellMap
open TunnellMap.OrderedGenerator
variable {n : ℤ} {p : Triple}

theorem TunnellMap.OrderedGenerator.q_mem_search_bounds {n A q : ℤ} (hn : 0 < n) (hA : 0 < A)
    (hq : q ^ 2 * A < n) : -n ≤ q ∧ q ≤ n := by sorry
