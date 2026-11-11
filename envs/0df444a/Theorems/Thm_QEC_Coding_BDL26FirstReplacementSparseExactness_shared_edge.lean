-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_shared_edge
-- name    : QEC.Coding.BDL26FirstReplacementSparseExactness.shared_edge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:13:08.635662+00:00
-- url     : https://prove2.me/theorems/6fef05f0-910d-4233-b2d4-6e0fa684cfa6
-- title:
--   BDL26 First Replacement Sparse Exactness: shared edge
-- statement:
--   The BDL26 First Replacement Sparse Exactness construction uses the shared edge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L80-L83
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L80-L83

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

theorem QEC.Coding.BDL26FirstReplacementSparseExactness.shared_edge (b : Fin 2) :
    xStarFaceXQEdge Seed center (oldFace b) 1 =
      xStarFaceXQEdge Seed center (oldFace 0) 1 := by sorry
