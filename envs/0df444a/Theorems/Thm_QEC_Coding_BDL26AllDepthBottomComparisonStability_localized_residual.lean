-- Prove2me | Theorems.Thm_QEC_Coding_BDL26AllDepthBottomComparisonStability_localized_residual
-- name    : QEC.Coding.BDL26AllDepthBottomComparisonStability.localized_residual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T14:12:42.698924+00:00
-- url     : https://prove2.me/theorems/e017bd92-583d-4dc3-ab6f-374c453bac12
-- title:
--   BDL26 All Depth Bottom Comparison Stability: localized residual
-- statement:
--   Actual whole-word telescoping, without any bottom-readout assumption.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/AllDepthBottomComparisonStability.lean#L160-L172
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/AllDepthBottomComparisonStability.lean#L160-L172

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

theorem QEC.Coding.BDL26AllDepthBottomComparisonStability.localized_residual (S : OddScale) (n : Nat) (sigma : TopInput S n)
    (e : TopWord S n) (x : (state S (n+2)).presentation.X)
    (support : hammingSupport e ⊆ BDL26LocalizedHistoryErrorDescent.star S n (TopIndex n) x) :
    residual S n sigma e =
      intervalMap1 (Data S n) 0 (TopIndex n) (Nat.zero_le _)
        ((BDL26LocalizedHistoryErrorDescent.actualDescent S n sigma e x support 0).word+
          baseComparison S n sigma+baseComparison S n (perturbTop S n sigma e))+
      (Data S n).family.coboundary0 (TopIndex n)
        (BDL26LocalizedHistoryErrorDescent.actualPotential S n sigma e x support 0 (TopIndex n)) := by sorry
