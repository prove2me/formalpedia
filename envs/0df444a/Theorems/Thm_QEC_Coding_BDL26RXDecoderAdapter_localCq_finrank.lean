-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_localCq_finrank
-- name    : QEC.Coding.BDL26RXDecoderAdapter.localCq_finrank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:47:18.29921+00:00
-- url     : https://prove2.me/theorems/45a50e9c-6a1e-4453-a3c1-e643711c8485
-- title:
--   BDL26 RXDecoder Adapter: local Cq finrank
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the local Cq finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/LocalComplexes.lean#L46-L50
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/LocalComplexes.lean#L46-L50

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Reindex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_LocalComplexes
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26RXDecoderAdapter.localCq_finrank (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (q : P.Q) :
    Module.finrank BDL26Field (localCq P S q).middleCohomology = 1 := by sorry
