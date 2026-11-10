-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_transpose_wordEquiv_symm
-- name    : QEC.Coding.BDL26RXDecoderAdapter.transpose_wordEquiv_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:04:51.398383+00:00
-- url     : https://prove2.me/theorems/546ac01f-74d1-4cc2-a57c-cf527bb28c24
-- title:
--   BDL26 RXDecoder Adapter: transpose word Equiv symm
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the transpose word Equiv symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Reindex.lean#L144-L147
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Reindex.lean#L144-L147

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Regions
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Reindex
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.transpose_wordEquiv_symm {A B : Type} [Fintype A] [Fintype B]
    (e : A ≃ B) : wordLinearMapTranspose (wordEquiv e).symm.toLinearMap =
      (wordEquiv e).toLinearMap := by sorry
