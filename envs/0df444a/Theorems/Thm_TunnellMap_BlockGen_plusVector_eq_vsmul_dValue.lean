-- Prove2me | Theorems.Thm_TunnellMap_BlockGen_plusVector_eq_vsmul_dValue
-- name    : TunnellMap.BlockGen.plusVector_eq_vsmul_dValue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:43:25.448302+00:00
-- url     : https://prove2.me/theorems/a8da5c3f-b9b3-5388-bcda-8e87f325daff
-- title:
--   Block Gen: plus Vector eq vsmul d Value
-- statement:
--   The reconstructed target of a generator index is the antipode of the
--   source, shifted by twice the retained midpoint direction; hence the plus
--   midpoint line of the resulting edge is that direction.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/RecordSign.lean#L30-L36
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/RecordSign.lean#L30-L36

import Definitions.Def_TunnellMap_BlockGeneratorCorrect
import Definitions.Def_TunnellMap_CanonicalSignLift
import Definitions.Def_TunnellMap_RecordSign
set_option autoImplicit true
open TunnellMap
open TunnellMap.BlockGen
open OrderedGenerator
variable {n : ℤ} {s : BResidual n}

theorem TunnellMap.BlockGen.plusVector_eq_vsmul_dValue
    (F : OrthogonalFrame (tau (residualSourceLift s))) (i : GeneratorIndex)
    {t : AResidual n} (ht : residualTargetLift t = targetValue s F i) :
    plusVector s t = vsmul (2 * i.q) (dValue F i) := by sorry
