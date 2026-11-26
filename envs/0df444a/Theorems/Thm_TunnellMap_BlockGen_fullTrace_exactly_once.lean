-- Prove2me | Theorems.Thm_TunnellMap_BlockGen_fullTrace_exactly_once
-- name    : TunnellMap.BlockGen.fullTrace_exactly_once
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:49:22.88291+00:00
-- url     : https://prove2.me/theorems/22f9cd73-bc3a-575e-a996-49d7b6e5b88a
-- title:
--   Block Gen: full Trace exactly once
-- statement:
--   **Exact-once emission.**  Every residual target orbit is emitted by the
--   generator at exactly one position of its complete trace.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/BlockGeneratorCorrect.lean#L547-L564
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/BlockGeneratorCorrect.lean#L547-L564

import Definitions.Def_TunnellMap_BlockGenerator
import Definitions.Def_TunnellMap_BlockGeneratorCorrect
set_option autoImplicit true
open TunnellMap
open TunnellMap.BlockGen
open OrderedGenerator
variable {n : ℤ} {p : Triple}
variable {s : BResidual n}

theorem TunnellMap.BlockGen.fullTrace_exactly_once (hn : Odd n) (hnpos : 0 < n)
    (F : OrthogonalFrame (tau (residualSourceLift s)))
    (tOrbit : (aResidualInvolution n hnpos).Orbit) :
    ∃! k : Fin (fullTrace s F).length,
      ((fullTrace s F).get k).target = orbitTargetLift hnpos tOrbit := by sorry
