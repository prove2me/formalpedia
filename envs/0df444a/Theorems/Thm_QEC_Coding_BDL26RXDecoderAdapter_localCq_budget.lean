-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_localCq_budget
-- name    : QEC.Coding.BDL26RXDecoderAdapter.localCq_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:56:46.885722+00:00
-- url     : https://prove2.me/theorems/595a6c52-44de-4efe-91d3-8a3829b2f8fb
-- title:
--   BDL26 RXDecoder Adapter: local Cq budget
-- statement:
--   F12 on the actual Q fibre, retaining all doubled-Z coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Budgets.lean#L42-L66
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Budgets.lean#L42-L66

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Budgets
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.localCq_budget (P : TannerSquarePresentation) (S : OddScale) (q : P.Q)
    (s : Word BDL26Field (LocalRegionIndex ((localQ P S).syndromeRegion q)))
    (hs : s ∈ LinearMap.range (wordLinearMapTranspose (localCq P S q).boundary2)) :
    ∃ f : Word BDL26Field (LocalRegionIndex ((localQ P S).correctionRegion q)),
      wordLinearMapTranspose (localCq P S q).boundary2 f = s ∧
        HammingWeight (qFlow P S q ((wordEquiv (qCorrectionEquiv P S q)).symm f)) ≤
          HammingWeight s := by sorry
