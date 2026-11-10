-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_wordEquiv_weight
-- name    : QEC.Coding.BDL26RXDecoderAdapter.wordEquiv_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:05:20.306205+00:00
-- url     : https://prove2.me/theorems/02cdd150-f7b1-4c4c-a948-e138168ccb63
-- title:
--   BDL26 RXDecoder Adapter: word Equiv weight
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the word Equiv weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Reindex.lean#L172-L181
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Reindex.lean#L172-L181

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Regions
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Reindex
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.wordEquiv_weight {A B : Type} [Fintype A] [Fintype B] (e : A ≃ B)
    (w : Word BDL26Field A) : HammingWeight (wordEquiv e w) = HammingWeight w := by sorry
