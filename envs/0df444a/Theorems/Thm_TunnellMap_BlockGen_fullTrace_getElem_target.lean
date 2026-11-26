-- Prove2me | Theorems.Thm_TunnellMap_BlockGen_fullTrace_getElem_target
-- name    : TunnellMap.BlockGen.fullTrace_getElem_target
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:29:55.308798+00:00
-- url     : https://prove2.me/theorems/bc48543d-f359-59f3-a5d6-d2e6e5f1c861
-- title:
--   Block Gen: full Trace get Elem target
-- statement:
--   The Block Gen construction uses the full Trace get Elem target property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/BlockGeneratorCorrect.lean#L516-L528
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/BlockGeneratorCorrect.lean#L516-L528

import Definitions.Def_TunnellMap_BlockGenerator
import Definitions.Def_TunnellMap_BlockGeneratorCorrect
set_option autoImplicit true
open TunnellMap
open TunnellMap.BlockGen
open OrderedGenerator
variable {n : ℤ} {p : Triple}
variable {s : BResidual n}

theorem TunnellMap.BlockGen.fullTrace_getElem_target (hnpos : 0 < n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) {k : ℕ}
    (hk : k < (fullTrace s F).length) :
    ((fullTrace s F)[k]'hk).target =
      orbitTargetLift hnpos ((incidentStream hnpos s F)[k]'(by
        rw [← fullTrace_length_eq hnpos F]; exact hk)) := by sorry
