-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_localDelta1_at_z
-- name    : QEC.Coding.BDL26RXDecoderAdapter.localDelta1_at_z
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:26:36.986823+00:00
-- url     : https://prove2.me/theorems/bfb1016c-dd81-4e93-866a-eeceb11c92bd
-- title:
--   BDL26 RXDecoder Adapter: local Delta1 at z
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the local Delta1 at z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Decomposition.lean#L48-L54
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Decomposition.lean#L48-L54

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Decomposition
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.localDelta1_at_z (P : TannerSquarePresentation) (S : OddScale)
    (w : Word BDL26Field (RX1 P S)) (z : P.Z) (c : Fin 2) :
    rxLocalDelta1 P S w (Sum.inr (z,c)) = 0 := by sorry
