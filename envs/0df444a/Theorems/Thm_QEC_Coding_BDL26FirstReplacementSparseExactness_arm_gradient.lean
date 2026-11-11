-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_arm_gradient
-- name    : QEC.Coding.BDL26FirstReplacementSparseExactness.arm_gradient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:16:08.629129+00:00
-- url     : https://prove2.me/theorems/9f4bcde5-fc4a-45ea-a8ca-4ae4c9dce100
-- title:
--   BDL26 First Replacement Sparse Exactness: arm gradient
-- statement:
--   The BDL26 First Replacement Sparse Exactness construction uses the arm gradient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L327-L333
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L327-L333

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

theorem QEC.Coding.BDL26FirstReplacementSparseExactness.arm_gradient (S : OddScale) (large : 16 ≤ S.half) (k : Fin 15)
    (b : Fin 2) (p : V S) :
    rxCoboundary0 Seed S p (arm S large k b)=p (armVertex S large k b) := by sorry
