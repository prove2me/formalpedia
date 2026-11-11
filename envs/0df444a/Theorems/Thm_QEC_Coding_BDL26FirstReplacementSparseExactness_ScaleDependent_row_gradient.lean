-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_ScaleDependent_row_gradient
-- name    : QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent.row_gradient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:28:13.827502+00:00
-- url     : https://prove2.me/theorems/2fe3fc6e-d3a7-4e54-a38b-2c8977eb9b97
-- title:
--   Scale Dependent: row gradient
-- statement:
--   The Scale Dependent construction uses the row gradient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L1046-L1051
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L1046-L1051

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

theorem QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent.row_gradient (S : OddScale) (n : Nat) (large : n+2 ≤ S.half) (k : Fin (n+1))
    (b : Fin 2) (p : V S) :
    (∑ i : Fin S.half, rxCoboundary0 Seed S p (horizontal S n large k b i))=
      p (grid S n large k b 0)+p (grid S n large k b (Fin.last S.half)) := by sorry
