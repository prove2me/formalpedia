-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_comparison_corrects_weight_seven_code
-- name    : QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.comparison_corrects_weight_seven_code
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:24:46.825295+00:00
-- url     : https://prove2.me/theorems/a8e25d9d-305c-483a-a9d7-0cc7f63bb850
-- title:
--   BDL26 Bottom Local First Min Weight Comparison: comparison corrects weight seven code
-- statement:
--   The same full result in the original physical C2 check-code interface.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L863-L867
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L863-L867

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Equivalence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BottomLocalFirstMinWeightComparison
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BottomLocalFirstMinWeightComparison
open BDL26FiniteTannerSquare BDL26FiniteAlternatingCore BDL26DecodingGraph
open BDL26TannerLocalRegularity BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26ReplacementCochainMaps BDL26LevelTwoCode BDL26LevelTwoDistance
open BDL26LevelTwoDecoder
open scoped BigOperators

theorem QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.comparison_corrects_weight_seven_code (S : OddScale) (large : 16 ≤ S.half)
    (e : Error S) (small : HammingWeight e ≤ 7) :
    e+ownerFirstMinWeightFallback S (tannerCoboundary1 (P2 S) e) ∈
      (levelTwoChainComplex S).firstCoboundaryCheckCode.carrier := by sorry
