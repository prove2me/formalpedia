-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_exact_of_zero_slice
-- name    : QEC.Coding.BDL26FirstReplacementSparseExactness.exact_of_zero_slice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:17:14.550515+00:00
-- url     : https://prove2.me/theorems/b75ca88a-95d2-4e72-90ff-b1959ceb612e
-- title:
--   BDL26 First Replacement Sparse Exactness: exact of zero slice
-- statement:
--   A zero slice of a complete actual cocycle constructs its full potential.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L358-L394
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L358-L394

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

theorem QEC.Coding.BDL26FirstReplacementSparseExactness.exact_of_zero_slice (S : OddScale) (large : 16 ≤ S.half)
    (w : W S) (closed : tannerCoboundary1 (rxReplacementPresentation Seed S) w=0)
    (k : Fin 15) (zero : sliceReadout S large k w=0) :
    ∃ p : V S, tannerCoboundary0 (rxReplacementPresentation Seed S) p=w := by sorry
