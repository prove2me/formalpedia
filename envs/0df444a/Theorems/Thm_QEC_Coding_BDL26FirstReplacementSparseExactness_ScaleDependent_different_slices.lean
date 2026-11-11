-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_ScaleDependent_different_slices
-- name    : QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent.different_slices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:26:47.898291+00:00
-- url     : https://prove2.me/theorems/2666c7bf-4f9e-4870-91e8-fda598f2e13f
-- title:
--   Scale Dependent: different slices
-- statement:
--   The Scale Dependent construction uses the different slices property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L976-L980
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L976-L980

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

theorem QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent.different_slices (S : OddScale) (n : Nat) (large : n+2 ≤ S.half)
    (k l : Fin (n+1)) (a b : Atom S)
    (same : atom S n large k a=atom S n large l b) : k=l := by sorry
