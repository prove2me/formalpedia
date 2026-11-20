-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NonzeroBackgroundComparisonStability_terminalPotential_spec
-- name    : QEC.Coding.BDL26NonzeroBackgroundComparisonStability.terminalPotential_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T14:24:20.506851+00:00
-- url     : https://prove2.me/theorems/7985b431-40d6-41db-9cc8-0b89518b63bb
-- title:
--   BDL26 Nonzero Background Comparison Stability: terminal Potential spec
-- statement:
--   The BDL26 Nonzero Background Comparison Stability construction uses the terminal Potential spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NonzeroBackgroundComparisonStability.lean#L265-L275
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NonzeroBackgroundComparisonStability.lean#L265-L275

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_AllDepthBottomComparisonStability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NonzeroBackgroundComparisonStability
import Theorems.Thm_QEC_Coding_BDL26AllDepthBottomComparisonStability_terminalPotential_spec
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_suffix_delta0
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_suffix_delta1

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26NonzeroBackgroundComparisonStability
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26HistoryLogicalResidual (suffix_delta0 suffix_delta1)
open BDL26RZMap1CoordinateBridge
open scoped Classical BigOperators

theorem QEC.Coding.BDL26NonzeroBackgroundComparisonStability.terminalPotential_spec (S : OddScale) (n : Nat) (B : Nat)
    (large : 14*B+16 ≤ S.half) (sigma0 : TopInput S n)
    (zero : BDL26AllDepthBottomComparisonStability.baseReadout S n sigma0=0) (g : TopWord S n)
    (budget : HammingWeight g ≤ B) (e : TopWord S n) (x : (state S (n+2)).presentation.X)
    (support : hammingSupport e ⊆ BDL26LocalizedHistoryErrorDescent.star S n (TopIndex n) x) :
    (Data S n).family.coboundary0 0
      (terminalPotential S n B large sigma0 zero g budget e x support)=
      (BDL26LocalizedHistoryErrorDescent.actualDescent S n (perturbTop S n sigma0 g) e x support 0).word+
        BDL26AllDepthBottomComparisonStability.baseComparison S n (perturbTop S n sigma0 g)+
        BDL26AllDepthBottomComparisonStability.baseComparison S n (perturbTop S n (perturbTop S n sigma0 g) e) := by sorry
