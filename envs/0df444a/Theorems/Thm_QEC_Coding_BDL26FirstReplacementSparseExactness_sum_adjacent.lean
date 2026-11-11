-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_sum_adjacent
-- name    : QEC.Coding.BDL26FirstReplacementSparseExactness.sum_adjacent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:15:14.111188+00:00
-- url     : https://prove2.me/theorems/c8267ad1-61dc-424d-9880-2767e0eb3237
-- title:
--   BDL26 First Replacement Sparse Exactness: sum adjacent
-- statement:
--   The full endpoint telescoping identity in characteristic two.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L204-L218
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L204-L218

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Equivalence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BottomLocalFirstMinWeightComparison
import Theorems.Thm_QEC_Coding_BDL26XLocalRadialParity_sum_adjacent

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FirstReplacementSparseExactness
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementCochainMaps BDL26RZMap1CoordinateBridge
open scoped Classical BigOperators

theorem QEC.Coding.BDL26FirstReplacementSparseExactness.sum_adjacent (n : Nat) (f : Fin (n+1) → Bit) :
    (∑ i : Fin n, (f i.castSucc+f i.succ))=f 0+f (Fin.last n) := by sorry
