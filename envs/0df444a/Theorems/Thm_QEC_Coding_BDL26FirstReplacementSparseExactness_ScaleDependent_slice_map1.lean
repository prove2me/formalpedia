-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_ScaleDependent_slice_map1
-- name    : QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent.slice_map1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:30:41.078632+00:00
-- url     : https://prove2.me/theorems/8ce89c4b-44e6-480c-b351-fb62c659dd8e
-- title:
--   Scale Dependent: slice map1
-- statement:
--   The auxiliary X-edge values are zero; each actual Q vertex reads its old Q.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L1155-L1162
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L1155-L1162

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

theorem QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent.slice_map1 (S : OddScale) (n : Nat) (large : n+2 ≤ S.half) (k : Fin (n+1))
    (v : Word Bit Seed.Q) :
    sliceReadout S n large k (rxMap1Coord Seed S v)=BDL26SeedCohomology.coefficient v := by sorry
