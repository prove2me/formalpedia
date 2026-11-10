-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_reindex_delta1
-- name    : QEC.Coding.BDL26RXDecoderAdapter.reindex_delta1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:04:48.8431+00:00
-- url     : https://prove2.me/theorems/02f985c1-a7cc-4c28-b33f-8ad7c52358d6
-- title:
--   BDL26 RXDecoder Adapter: reindex delta1
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the reindex delta1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Reindex.lean#L161-L167
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Reindex.lean#L161-L167

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Regions
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Reindex
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open MultiscaleDecoder
open scoped Classical BigOperators
variable {A0 A1 A2 B0 B1 B2 : Type}
variable [Fintype A0] [Fintype A1] [Fintype A2]
variable [Fintype B0] [Fintype B1] [Fintype B2]

theorem QEC.Coding.BDL26RXDecoderAdapter.reindex_delta1 (K : ChainComplexData BDL26Field (Word BDL26Field A0)
    (Word BDL26Field A1) (Word BDL26Field A2))
    (e0 : A0 ≃ B0) (e1 : A1 ≃ B1) (e2 : A2 ≃ B2) :
    wordLinearMapTranspose (reindexComplex K e0 e1 e2).boundary2 =
      (wordEquiv e2).toLinearMap.comp
        ((wordLinearMapTranspose K.boundary2).comp (wordEquiv e1).symm.toLinearMap) := by sorry
