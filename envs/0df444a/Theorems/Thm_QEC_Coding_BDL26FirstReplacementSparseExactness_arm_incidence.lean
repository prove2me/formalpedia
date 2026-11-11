-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_arm_incidence
-- name    : QEC.Coding.BDL26FirstReplacementSparseExactness.arm_incidence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:15:28.728615+00:00
-- url     : https://prove2.me/theorems/a4ff42a1-9442-469c-b0f6-598712dbb6f0
-- title:
--   BDL26 First Replacement Sparse Exactness: arm incidence
-- statement:
--   Whole original degree-one matrix column for each shifted interior vertex.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L304-L325
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L304-L325

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

theorem QEC.Coding.BDL26FirstReplacementSparseExactness.arm_incidence (S : OddScale) (large : 16 ≤ S.half) (k : Fin 15)
    (b : Fin 2) (v : RX0 Seed S) :
    rxBoundary1Matrix Seed S v (arm S large k b)=
      if v=armVertex S large k b then 1 else 0 := by sorry
