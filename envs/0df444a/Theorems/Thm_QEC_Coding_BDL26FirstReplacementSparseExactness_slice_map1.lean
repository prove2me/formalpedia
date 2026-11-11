-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_slice_map1
-- name    : QEC.Coding.BDL26FirstReplacementSparseExactness.slice_map1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:17:05.157623+00:00
-- url     : https://prove2.me/theorems/535eba03-89a0-4e50-8ced-dbf260b97baa
-- title:
--   BDL26 First Replacement Sparse Exactness: slice map1
-- statement:
--   The auxiliary X-edge values are zero; each actual Q vertex reads its old Q.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L348-L355
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L348-L355

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Equivalence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BottomLocalFirstMinWeightComparison
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FirstReplacementSparseExactness
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementCochainMaps BDL26RZMap1CoordinateBridge
open scoped Classical BigOperators

theorem QEC.Coding.BDL26FirstReplacementSparseExactness.slice_map1 (S : OddScale) (large : 16 ≤ S.half) (k : Fin 15)
    (v : Word Bit Seed.Q) :
    sliceReadout S large k (rxMap1Coord Seed S v)=BDL26SeedCohomology.coefficient v := by sorry
