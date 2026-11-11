-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_ScaleDependent_arm_gradient
-- name    : QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent.arm_gradient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:30:01.172499+00:00
-- url     : https://prove2.me/theorems/7c840d8f-003f-4dc5-a7c4-4673d30297c2
-- title:
--   Scale Dependent: arm gradient
-- statement:
--   The Scale Dependent construction uses the arm gradient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L1134-L1140
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L1134-L1140

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

theorem QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent.arm_gradient (S : OddScale) (n : Nat) (large : n+2 ≤ S.half) (k : Fin (n+1))
    (b : Fin 2) (p : V S) :
    rxCoboundary0 Seed S p (arm S n large k b)=p (armVertex S n large k b) := by sorry
