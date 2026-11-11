-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_ScaleDependent_zero_slice_readout
-- name    : QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent.zero_slice_readout
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:28:05.155655+00:00
-- url     : https://prove2.me/theorems/771b06ce-1b39-45bf-a837-dbd4a3b12659
-- title:
--   Scale Dependent: zero slice readout
-- statement:
--   The Scale Dependent construction uses the zero slice readout property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L1017-L1025
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L1017-L1025

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

theorem QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent.zero_slice_readout (S : OddScale) (n : Nat) (large : n+2 ≤ S.half) (k : Fin (n+1)) (w : W S)
    (zero : ∀ a : Atom S, w (atom S n large k a)=0) : sliceReadout S n large k w=0 := by sorry
