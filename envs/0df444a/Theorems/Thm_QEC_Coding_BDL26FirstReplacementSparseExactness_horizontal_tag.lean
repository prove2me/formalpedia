-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_horizontal_tag
-- name    : QEC.Coding.BDL26FirstReplacementSparseExactness.horizontal_tag
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:14:36.718253+00:00
-- url     : https://prove2.me/theorems/130c23de-9222-4ddb-aea0-c73ed55d23df
-- title:
--   BDL26 First Replacement Sparse Exactness: horizontal tag
-- statement:
--   The BDL26 First Replacement Sparse Exactness construction uses the horizontal tag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L113-L126
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L113-L126

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

theorem QEC.Coding.BDL26FirstReplacementSparseExactness.horizontal_tag (S : OddScale) (large : 16 ≤ S.half) (k : Fin 15)
    (b : Fin 2) (i : Fin S.half) :
    horizontal S large k b i =
      .inl ⟨center,.inl (0,.inr (.inl (oldFace b,i,sliceIndex S large k)))⟩ := by sorry
