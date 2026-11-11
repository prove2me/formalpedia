-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_exists_zero_slice
-- name    : QEC.Coding.BDL26FirstReplacementSparseExactness.exists_zero_slice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:14:30.150262+00:00
-- url     : https://prove2.me/theorems/90281c11-5834-476b-b3b1-ec3c9210c956
-- title:
--   BDL26 First Replacement Sparse Exactness: exists zero slice
-- statement:
--   Direct finite pigeonhole argument on the whole original word support.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L154-L176
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L154-L176

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

theorem QEC.Coding.BDL26FirstReplacementSparseExactness.exists_zero_slice (S : OddScale) (large : 16 ≤ S.half) (w : W S)
    (small : HammingWeight w ≤ 14) :
    ∃ k : Fin 15, ∀ a : Atom S, w (atom S large k a)=0 := by sorry
