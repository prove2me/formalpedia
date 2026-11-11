-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_ScaleDependent_arm_subdivision_incidence
-- name    : QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent.arm_subdivision_incidence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:28:05.621303+00:00
-- url     : https://prove2.me/theorems/47c77b8d-be30-4363-84df-c31b22718507
-- title:
--   Scale Dependent: arm subdivision incidence
-- statement:
--   All original subdivision-vertex tags, including both kinds of old edge.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L1093-L1108
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L1093-L1108

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

theorem QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent.arm_subdivision_incidence (S : OddScale) (n : Nat) (large : n+2 ≤ S.half) (k : Fin (n+1))
    (b : Fin 2) (v : SubdivisionVertex Seed center S) :
    qSubdivisionVertexXIncidence Seed (oldQ b) center S v
      (.inr (armEdge b,sliceIndex S n large k)) =
      if v = .inr (.inl
        (xStarFaceQZEdge Seed center (oldFace b) 0,sliceIndex S n large k)) then 1 else 0 := by sorry
