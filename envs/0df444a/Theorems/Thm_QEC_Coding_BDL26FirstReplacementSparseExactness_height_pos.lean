-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_height_pos
-- name    : QEC.Coding.BDL26FirstReplacementSparseExactness.height_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:13:53.348673+00:00
-- url     : https://prove2.me/theorems/04617a45-c2c1-471f-ba89-4f751598db50
-- title:
--   BDL26 First Replacement Sparse Exactness: height pos
-- statement:
--   The BDL26 First Replacement Sparse Exactness construction uses the height pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L97-L98
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L97-L98

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

theorem QEC.Coding.BDL26FirstReplacementSparseExactness.height_pos (S : OddScale) (large : 16 ≤ S.half) (k : Fin 15) :
    0 < (height S large k).val := by sorry
