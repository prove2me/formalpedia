-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_horizontal_gradient
-- name    : QEC.Coding.BDL26FirstReplacementSparseExactness.horizontal_gradient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:14:44.66946+00:00
-- url     : https://prove2.me/theorems/dd24e7f3-ce33-498e-8ed7-096522dc3172
-- title:
--   BDL26 First Replacement Sparse Exactness: horizontal gradient
-- statement:
--   The BDL26 First Replacement Sparse Exactness construction uses the horizontal gradient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L224-L237
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L224-L237

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

theorem QEC.Coding.BDL26FirstReplacementSparseExactness.horizontal_gradient (S : OddScale) (large : 16 ≤ S.half) (k : Fin 15)
    (b : Fin 2) (i : Fin S.half) (p : V S) :
    rxCoboundary0 Seed S p (horizontal S large k b i)=
      p (grid S large k b i.castSucc)+p (grid S large k b i.succ) := by sorry
