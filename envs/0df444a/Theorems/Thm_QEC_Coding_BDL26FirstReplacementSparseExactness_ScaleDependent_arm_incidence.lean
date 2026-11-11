-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_ScaleDependent_arm_incidence
-- name    : QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent.arm_incidence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:32:07.893214+00:00
-- url     : https://prove2.me/theorems/f492d99a-a7de-4cce-9cd2-0e946636d7f8
-- title:
--   Scale Dependent: arm incidence
-- statement:
--   Whole original degree-one matrix column for each shifted interior vertex.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L1111-L1132
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L1111-L1132

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

theorem QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent.arm_incidence (S : OddScale) (n : Nat) (large : n+2 ≤ S.half) (k : Fin (n+1))
    (b : Fin 2) (v : RX0 Seed S) :
    rxBoundary1Matrix Seed S v (arm S n large k b)=
      if v=armVertex S n large k b then 1 else 0 := by sorry
