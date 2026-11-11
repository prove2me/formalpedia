-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_ScaleDependent_sliceReadout_apply
-- name    : QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent.sliceReadout_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:49:27.946703+00:00
-- url     : https://prove2.me/theorems/ee4f0f03-ea29-4191-90e6-00cedcd7eadd
-- title:
--   Scale Dependent: slice Readout apply
-- statement:
--   The Scale Dependent construction uses the slice Readout apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L1011-L1015
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L1011-L1015

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

theorem QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent.sliceReadout_apply (S : OddScale) (n : Nat) (large : n+2 ≤ S.half) (k : Fin (n+1)) (w : W S) :
    sliceReadout S n large k w =
      ∑ b : Fin 2, (w (arm S n large k b)+∑ i : Fin S.half, w (horizontal S n large k b i)) := by sorry
