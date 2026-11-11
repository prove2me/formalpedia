-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_ScaleDependent_slice_boundary
-- name    : QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent.slice_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:30:59.299067+00:00
-- url     : https://prove2.me/theorems/e9900227-e75d-4b70-a5d2-d2f0f92c2b88
-- title:
--   Scale Dependent: slice boundary
-- statement:
--   Every slice annihilates every full raw boundary, with both row endpoints.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L1143-L1152
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L1143-L1152

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

theorem QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent.slice_boundary (S : OddScale) (n : Nat) (large : n+2 ≤ S.half) (k : Fin (n+1)) (p : V S) :
    sliceReadout S n large k (rxCoboundary0 Seed S p)=0 := by sorry
