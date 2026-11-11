-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_slice_boundary
-- name    : QEC.Coding.BDL26FirstReplacementSparseExactness.slice_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:15:38.426486+00:00
-- url     : https://prove2.me/theorems/3f28393d-2c44-485c-af02-3204eafb79bf
-- title:
--   BDL26 First Replacement Sparse Exactness: slice boundary
-- statement:
--   Every slice annihilates every full raw boundary, with both row endpoints.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L336-L345
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L336-L345

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

theorem QEC.Coding.BDL26FirstReplacementSparseExactness.slice_boundary (S : OddScale) (large : 16 ≤ S.half) (k : Fin 15) (p : V S) :
    sliceReadout S large k (rxCoboundary0 Seed S p)=0 := by sorry
