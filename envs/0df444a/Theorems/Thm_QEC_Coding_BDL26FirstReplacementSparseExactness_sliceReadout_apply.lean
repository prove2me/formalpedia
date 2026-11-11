-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_sliceReadout_apply
-- name    : QEC.Coding.BDL26FirstReplacementSparseExactness.sliceReadout_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:04:15.068356+00:00
-- url     : https://prove2.me/theorems/0c511d30-19fd-4917-96e8-4f9fd0065971
-- title:
--   BDL26 First Replacement Sparse Exactness: slice Readout apply
-- statement:
--   The BDL26 First Replacement Sparse Exactness construction uses the slice Readout apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L187-L191
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L187-L191

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

theorem QEC.Coding.BDL26FirstReplacementSparseExactness.sliceReadout_apply (S : OddScale) (large : 16 ≤ S.half) (k : Fin 15) (w : W S) :
    sliceReadout S large k w =
      ∑ b : Fin 2, (w (arm S large k b)+∑ i : Fin S.half, w (horizontal S large k b i)) := by sorry
