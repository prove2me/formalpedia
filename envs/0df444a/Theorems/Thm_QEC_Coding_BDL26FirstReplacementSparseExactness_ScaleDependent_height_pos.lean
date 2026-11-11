-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_ScaleDependent_height_pos
-- name    : QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent.height_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:25:37.111501+00:00
-- url     : https://prove2.me/theorems/3ffb70a9-60d0-4acf-86ff-6a4ba18b2dee
-- title:
--   Scale Dependent: height pos
-- statement:
--   The Scale Dependent construction uses the height pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L933-L934
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L933-L934

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

theorem QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent.height_pos (S : OddScale) (n : Nat) (large : n+2 ≤ S.half) (k : Fin (n+1)) :
    0 < (height S n large k).val := by sorry
