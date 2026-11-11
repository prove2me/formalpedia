-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_different_slices
-- name    : QEC.Coding.BDL26FirstReplacementSparseExactness.different_slices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:15:39.759128+00:00
-- url     : https://prove2.me/theorems/8e0aa8fe-3572-4545-90a4-f0594db550b3
-- title:
--   BDL26 First Replacement Sparse Exactness: different slices
-- statement:
--   The BDL26 First Replacement Sparse Exactness construction uses the different slices property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L147-L151
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L147-L151

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

theorem QEC.Coding.BDL26FirstReplacementSparseExactness.different_slices (S : OddScale) (large : 16 ≤ S.half)
    (k l : Fin 15) (a b : Atom S)
    (same : atom S large k a=atom S large l b) : k=l := by sorry
