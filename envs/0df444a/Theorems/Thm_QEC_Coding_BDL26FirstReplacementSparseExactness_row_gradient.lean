-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_row_gradient
-- name    : QEC.Coding.BDL26FirstReplacementSparseExactness.row_gradient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:15:11.950196+00:00
-- url     : https://prove2.me/theorems/b494c22a-0bbd-4af5-8b64-fffca2f6449f
-- title:
--   BDL26 First Replacement Sparse Exactness: row gradient
-- statement:
--   The BDL26 First Replacement Sparse Exactness construction uses the row gradient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L239-L244
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L239-L244

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

theorem QEC.Coding.BDL26FirstReplacementSparseExactness.row_gradient (S : OddScale) (large : 16 ≤ S.half) (k : Fin 15)
    (b : Fin 2) (p : V S) :
    (∑ i : Fin S.half, rxCoboundary0 Seed S p (horizontal S large k b i))=
      p (grid S large k b 0)+p (grid S large k b (Fin.last S.half)) := by sorry
