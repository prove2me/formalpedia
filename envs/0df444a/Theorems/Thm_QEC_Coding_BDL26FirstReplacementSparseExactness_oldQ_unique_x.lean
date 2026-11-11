-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_oldQ_unique_x
-- name    : QEC.Coding.BDL26FirstReplacementSparseExactness.oldQ_unique_x
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:05:30.347517+00:00
-- url     : https://prove2.me/theorems/8fe6a1e2-e694-4a08-a564-1a713a4300b6
-- title:
--   BDL26 First Replacement Sparse Exactness: old Q unique x
-- statement:
--   The BDL26 First Replacement Sparse Exactness construction uses the old Q unique x property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L42-L78
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L42-L78

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

theorem QEC.Coding.BDL26FirstReplacementSparseExactness.oldQ_unique_x (b : Fin 2) (x : Seed.X) :
    Seed.xq x (oldQ b)=true ↔ x=center := by sorry
