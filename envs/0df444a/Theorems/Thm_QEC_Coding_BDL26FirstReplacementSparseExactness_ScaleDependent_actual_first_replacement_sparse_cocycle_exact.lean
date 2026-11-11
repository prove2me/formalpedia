-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_ScaleDependent_actual_first_replacement_sparse_cocycle_exact
-- name    : QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent.actual_first_replacement_sparse_cocycle_exact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:31:09.442689+00:00
-- url     : https://prove2.me/theorems/41b03af2-234a-434f-89e1-0db06c5166fb
-- title:
--   Scale Dependent: actual first replacement sparse cocycle exact
-- statement:
--   Every complete first-replacement cocycle of weight at most k is exact.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L1205-L1214
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L1205-L1214

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Equivalence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BottomLocalFirstMinWeightComparison
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FirstReplacementSparseExactness QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementCochainMaps BDL26RZMap1CoordinateBridge
open scoped Classical BigOperators

theorem QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent.actual_first_replacement_sparse_cocycle_exact (S : OddScale) (k : Nat)
    (large : k+2 ≤ S.half)
    (w : Word Bit (BDL26DecodingGraph.state S 1).presentation.Q)
    (closed : tannerCoboundary1 (BDL26DecodingGraph.state S 1).presentation w=0)
    (small : HammingWeight w≤k) :
    w ∈ LinearMap.range (tannerCoboundary0 (BDL26DecodingGraph.state S 1).presentation) := by sorry
