-- Prove2me | Theorems.Thm_TunnellMap_BlockGen_fullTrace_getElem_key
-- name    : TunnellMap.BlockGen.fullTrace_getElem_key
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:32:43.739987+00:00
-- url     : https://prove2.me/theorems/ea80e1f1-81c0-47e7-9fb9-b40f1f756a68
-- title:
--   Block Gen: full Trace get Elem key
-- statement:
--   The Block Gen construction uses the full Trace get Elem key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/BlockGeneratorCorrect.lean#L530-L543
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/BlockGeneratorCorrect.lean#L530-L543

import Definitions.Def_TunnellMap_BlockGenerator
import Definitions.Def_TunnellMap_BlockGeneratorCorrect
set_option autoImplicit true
open TunnellMap
open TunnellMap.BlockGen
open OrderedGenerator
variable {n : ℤ} {p : Triple}
variable {s : BResidual n}

theorem TunnellMap.BlockGen.fullTrace_getElem_key (hnpos : 0 < n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) {k : ℕ}
    (hk : k < (fullTrace s F).length) :
    ((fullTrace s F)[k]'hk).key =
      orbitEdgeKey hnpos ((bResidualInvolution n).orbit s)
        ((incidentStream hnpos s F)[k]'(by
          rw [← fullTrace_length_eq hnpos F]; exact hk)) := by sorry
