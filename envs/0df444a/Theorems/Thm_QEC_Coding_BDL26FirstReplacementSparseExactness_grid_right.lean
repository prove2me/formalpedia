-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_grid_right
-- name    : QEC.Coding.BDL26FirstReplacementSparseExactness.grid_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:15:19.208815+00:00
-- url     : https://prove2.me/theorems/b260df9b-4f7d-44a0-9165-60dcf72d5f53
-- title:
--   BDL26 First Replacement Sparse Exactness: grid right
-- statement:
--   The BDL26 First Replacement Sparse Exactness construction uses the grid right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L249-L264
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L249-L264

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

theorem QEC.Coding.BDL26FirstReplacementSparseExactness.grid_right (S : OddScale) (large : 16 ≤ S.half) (k : Fin 15) (b : Fin 2) :
    grid S large k b (Fin.last S.half)=armVertex S large k b := by sorry
