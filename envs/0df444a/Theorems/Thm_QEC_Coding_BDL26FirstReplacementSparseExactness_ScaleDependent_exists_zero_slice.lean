-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_ScaleDependent_exists_zero_slice
-- name    : QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent.exists_zero_slice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:26:57.82065+00:00
-- url     : https://prove2.me/theorems/c3d15a95-21eb-447b-b4cc-40305b7355c6
-- title:
--   Scale Dependent: exists zero slice
-- statement:
--   Direct finite pigeonhole argument on the whole original word support.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L983-L1005
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L983-L1005

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

theorem QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent.exists_zero_slice (S : OddScale) (n : Nat) (large : n+2 ≤ S.half) (w : W S)
    (small : HammingWeight w ≤ n) :
    ∃ k : Fin (n+1), ∀ a : Atom S, w (atom S n large k a)=0 := by sorry
