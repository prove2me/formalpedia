-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_zero_slice_readout
-- name    : QEC.Coding.BDL26FirstReplacementSparseExactness.zero_slice_readout
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:14:45.111306+00:00
-- url     : https://prove2.me/theorems/e264efae-04b1-4ef0-8b19-ddf9174d6d4d
-- title:
--   BDL26 First Replacement Sparse Exactness: zero slice readout
-- statement:
--   The BDL26 First Replacement Sparse Exactness construction uses the zero slice readout property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L193-L201
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L193-L201

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

theorem QEC.Coding.BDL26FirstReplacementSparseExactness.zero_slice_readout (S : OddScale) (large : 16 ≤ S.half) (k : Fin 15) (w : W S)
    (zero : ∀ a : Atom S, w (atom S large k a)=0) : sliceReadout S large k w=0 := by sorry
