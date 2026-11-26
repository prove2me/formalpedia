-- Prove2me | Theorems.Thm_TunnellMap_OrderedGenerator_incidentStream_nodup
-- name    : TunnellMap.OrderedGenerator.incidentStream_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:51:14.645489+00:00
-- url     : https://prove2.me/theorems/b4df2e1a-c3a0-5edd-8858-72ebed1ea665
-- title:
--   Ordered Generator: incident Stream nodup
-- statement:
--   The Ordered Generator construction uses the incident Stream nodup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrderedGenerator.lean#L481-L485
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrderedGenerator.lean#L481-L485

import Definitions.Def_TunnellMap_GeneratorSoundness
import Definitions.Def_TunnellMap_OrbitRanking
import Definitions.Def_TunnellMap_PreferenceList
import Definitions.Def_TunnellMap_OrderedGenerator
set_option autoImplicit true
open TunnellMap
open TunnellMap.OrderedGenerator
variable {n : ℤ} {p : Triple}

theorem TunnellMap.OrderedGenerator.incidentStream_nodup (hnpos : 0 < n) (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) :
    (incidentStream hnpos s F).Nodup := by sorry
