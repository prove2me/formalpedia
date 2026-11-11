-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_actual_first_replacement_sparse_cocycle_exact
-- name    : QEC.Coding.BDL26FirstReplacementSparseExactness.actual_first_replacement_sparse_cocycle_exact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:06:32.674883+00:00
-- url     : https://prove2.me/theorems/40133511-1b56-41d0-8f05-a01c0403ec12
-- title:
--   BDL26 First Replacement Sparse Exactness: actual first replacement sparse cocycle exact
-- statement:
--   Explicit H=16: no bound on a selected representative or a distance oracle.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L397-L405
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L397-L405

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

theorem QEC.Coding.BDL26FirstReplacementSparseExactness.actual_first_replacement_sparse_cocycle_exact (S : OddScale)
    (large : 16 ≤ S.half) (w : Word Bit (BDL26DecodingGraph.state S 1).presentation.Q)
    (closed : tannerCoboundary1 (BDL26DecodingGraph.state S 1).presentation w=0)
    (small : HammingWeight w≤14) :
    w ∈ LinearMap.range (tannerCoboundary0 (BDL26DecodingGraph.state S 1).presentation) := by sorry
