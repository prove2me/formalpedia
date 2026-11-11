-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_arm_subdivision_incidence
-- name    : QEC.Coding.BDL26FirstReplacementSparseExactness.arm_subdivision_incidence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:15:10.217773+00:00
-- url     : https://prove2.me/theorems/de8c3aa9-9096-44ff-8faf-9749ec22a4d1
-- title:
--   BDL26 First Replacement Sparse Exactness: arm subdivision incidence
-- statement:
--   All original subdivision-vertex tags, including both kinds of old edge.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L286-L301
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L286-L301

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

theorem QEC.Coding.BDL26FirstReplacementSparseExactness.arm_subdivision_incidence (S : OddScale) (large : 16 ≤ S.half) (k : Fin 15)
    (b : Fin 2) (v : SubdivisionVertex Seed center S) :
    qSubdivisionVertexXIncidence Seed (oldQ b) center S v
      (.inr (armEdge b,sliceIndex S large k)) =
      if v = .inr (.inl
        (xStarFaceQZEdge Seed center (oldFace b) 0,sliceIndex S large k)) then 1 else 0 := by sorry
