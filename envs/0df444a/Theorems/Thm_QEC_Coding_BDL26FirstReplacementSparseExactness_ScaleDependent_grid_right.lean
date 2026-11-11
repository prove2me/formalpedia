-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_ScaleDependent_grid_right
-- name    : QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent.grid_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:27:42.031052+00:00
-- url     : https://prove2.me/theorems/b827eec1-cd24-4fab-b7fa-b7e4a770a654
-- title:
--   Scale Dependent: grid right
-- statement:
--   The Scale Dependent construction uses the grid right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L1056-L1071
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L1056-L1071

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

theorem QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent.grid_right (S : OddScale) (n : Nat) (large : n+2 ≤ S.half) (k : Fin (n+1)) (b : Fin 2) :
    grid S n large k b (Fin.last S.half)=armVertex S n large k b := by sorry
