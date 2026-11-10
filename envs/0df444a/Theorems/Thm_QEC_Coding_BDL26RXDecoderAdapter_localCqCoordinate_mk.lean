-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_localCqCoordinate_mk
-- name    : QEC.Coding.BDL26RXDecoderAdapter.localCqCoordinate_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:53:48.925863+00:00
-- url     : https://prove2.me/theorems/4842fb63-4857-4c0d-963a-76019053a805
-- title:
--   BDL26 RXDecoder Adapter: local Cq Coordinate mk
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the local Cq Coordinate mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Representative.lean#L14-L26
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Representative.lean#L14-L26

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Representative
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.localCqCoordinate_mk (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (q : P.Q)
    (c : (localCq P S q).middleCocycleCode.carrier) :
    localCqCohomologyEquiv P A S q (Submodule.Quotient.mk c) =
      c.1 (qCorrectionEquiv P S q (0, Sum.inl (Sum.inl ()))) := by sorry
