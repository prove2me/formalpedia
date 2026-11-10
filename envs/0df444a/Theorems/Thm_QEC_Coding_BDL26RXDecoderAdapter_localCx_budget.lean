-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_localCx_budget
-- name    : QEC.Coding.BDL26RXDecoderAdapter.localCx_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:57:10.313911+00:00
-- url     : https://prove2.me/theorems/6d6a8f1e-adbf-4482-b24e-68f86dbf2fb5
-- title:
--   BDL26 RXDecoder Adapter: local Cx budget
-- statement:
--   F12 on the actual X fibre, with the global outgoing flow norm.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Budgets.lean#L13-L39
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Budgets.lean#L13-L39

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Budgets
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.localCx_budget (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) (x : P.X)
    (s : Word BDL26Field (LocalRegionIndex ((localX P S).syndromeRegion x)))
    (hs : s ∈ LinearMap.range (wordLinearMapTranspose (localCx P S x).boundary2)) :
    ∃ f : Word BDL26Field (LocalRegionIndex ((localX P S).correctionRegion x)),
      wordLinearMapTranspose (localCx P S x).boundary2 f = s ∧
        HammingWeight (xFlow P S x ((wordEquiv (xCorrectionEquiv P S x)).symm f)) ≤
          HammingWeight s := by sorry
