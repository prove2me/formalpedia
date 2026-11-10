-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_q_restrict_correction
-- name    : QEC.Coding.BDL26RXDecoderAdapter.q_restrict_correction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:47:36.3799+00:00
-- url     : https://prove2.me/theorems/4ebed595-0deb-4235-aa69-3460f88f6508
-- title:
--   BDL26 RXDecoder Adapter: q restrict correction
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the q restrict correction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Coordinates.lean#L21-L27
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Coordinates.lean#L21-L27

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_LocalComplexes
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.q_restrict_correction (P : TannerSquarePresentation) (S : OddScale) (q : P.Q)
    (w : Word BDL26Field (RX1 P S)) :
    (wordEquiv (qCorrectionEquiv P S q)).symm
      (restrictWordLinear ((localQ P S).correctionRegion q) w) =
        fun v => w (Sum.inr ⟨q,v⟩) := by sorry
