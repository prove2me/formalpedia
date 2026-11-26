-- Prove2me | Theorems.Thm_TunnellMap_BlockGen_target_eq_signAct_canonical
-- name    : TunnellMap.BlockGen.target_eq_signAct_canonical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:43:30.722831+00:00
-- url     : https://prove2.me/theorems/01e14f4f-cc2b-582b-adb2-b63cd8f96614
-- title:
--   Block Gen: target eq sign Act canonical
-- statement:
--   The reconstructed target of a retained index is the canonical
--   representative of its orbit, multiplied by the sign stored in the record.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/RecordSign.lean#L75-L97
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/RecordSign.lean#L75-L97

import Definitions.Def_TunnellMap_BlockGeneratorCorrect
import Definitions.Def_TunnellMap_CanonicalSignLift
import Definitions.Def_TunnellMap_RecordSign
set_option autoImplicit true
open TunnellMap
open TunnellMap.BlockGen
open OrderedGenerator
variable {n : ℤ} {s : BResidual n}

theorem TunnellMap.BlockGen.target_eq_signAct_canonical (hnpos : 0 < n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) (i : GeneratorIndex)
    {t : AResidual n} (ht : residualTargetLift t = targetValue s F i) :
    t = signActA hnpos ((recordOf s F i).sign)
      (canonicalAResidualRepresentative hnpos
        ((aResidualInvolution n hnpos).orbit t)) := by sorry
