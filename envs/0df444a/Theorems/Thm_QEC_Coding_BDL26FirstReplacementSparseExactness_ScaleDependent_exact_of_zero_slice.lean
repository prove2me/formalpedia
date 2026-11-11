-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_ScaleDependent_exact_of_zero_slice
-- name    : QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent.exact_of_zero_slice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:30:54.993369+00:00
-- url     : https://prove2.me/theorems/b5fa2b7c-54e7-4704-a86d-6e1156c227e1
-- title:
--   Scale Dependent: exact of zero slice
-- statement:
--   A zero slice of a complete actual cocycle constructs its full potential.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L1165-L1201
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L1165-L1201

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

theorem QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent.exact_of_zero_slice (S : OddScale) (n : Nat) (large : n+2 ≤ S.half)
    (w : W S) (closed : tannerCoboundary1 (rxReplacementPresentation Seed S) w=0)
    (k : Fin (n+1)) (zero : sliceReadout S n large k w=0) :
    ∃ p : V S, tannerCoboundary0 (rxReplacementPresentation Seed S) p=w := by sorry
