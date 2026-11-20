-- Prove2me | Theorems.Thm_QEC_Coding_BDL26AllDepthBottomComparisonStability_terminalPotential_spec
-- name    : QEC.Coding.BDL26AllDepthBottomComparisonStability.terminalPotential_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T14:09:22.173236+00:00
-- url     : https://prove2.me/theorems/8ba1699c-61e0-48fa-9062-c34977e996f9
-- title:
--   BDL26 All Depth Bottom Comparison Stability: terminal Potential spec
-- statement:
--   The BDL26 All Depth Bottom Comparison Stability construction uses the terminal Potential spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/AllDepthBottomComparisonStability.lean#L237-L244
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/AllDepthBottomComparisonStability.lean#L237-L244

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BottomLocalFirstMinWeightComparison
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalizedHistoryErrorDescent
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_ActualFailureReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_EvenC4OldXEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_AllDepthBottomComparisonStability
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26AllDepthBottomComparisonStability
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26HistoryLogicalResidual BDL26RZMap1CoordinateBridge
open scoped Classical BigOperators

theorem QEC.Coding.BDL26AllDepthBottomComparisonStability.terminalPotential_spec (S : OddScale) (n : Nat) (large : 16 ≤ S.half)
    (sigma : TopInput S n) (e : TopWord S n) (x : (state S (n+2)).presentation.X)
    (support : hammingSupport e ⊆ BDL26LocalizedHistoryErrorDescent.star S n (TopIndex n) x)
    (zero : baseReadout S n sigma=0) :
    (Data S n).family.coboundary0 0 (terminalPotential S n large sigma e x support zero)=
      (BDL26LocalizedHistoryErrorDescent.actualDescent S n sigma e x support 0).word+
        baseComparison S n sigma+baseComparison S n (perturbTop S n sigma e) := by sorry
