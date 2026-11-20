-- Prove2me | Theorems.Thm_QEC_Coding_BDL26AllDepthBottomComparisonStability_canonical_zero_base_instability
-- name    : QEC.Coding.BDL26AllDepthBottomComparisonStability.canonical_zero_base_instability
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T14:11:34.345731+00:00
-- url     : https://prove2.me/theorems/a8cecc99-b6ab-48a5-bc1c-bf63e271335c
-- title:
--   BDL26 All Depth Bottom Comparison Stability: canonical zero base instability
-- statement:
--   Canonical obstruction in the ORIGINAL sigma2=0 domain, uniform in scale.
--   It retains a genuine legal C4 input, one physical flip and the full residual.
--   The second bottom input is nonzero; replacing its decoder call can matter.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/AllDepthBottomComparisonStability.lean#L332-L348
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/AllDepthBottomComparisonStability.lean#L332-L348

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

theorem QEC.Coding.BDL26AllDepthBottomComparisonStability.canonical_zero_base_instability (S : OddScale) :
    ∃ (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S 2)
      (q : BDL26CSSHamiltonian.Physical S 4),
      BDL26CanonicalHistoryMarks.baseInput S 2 (BDL26ActualFailureReadout.input S 2 u)=0 ∧
      BDL26ActualFailureReadout.secondReadout S 2 u q≠0 ∧
      BDL26LogicalDefectProtection.chiX S 2 u q=1 ∧
      BDL26CSSHamiltonian.zSyndrome S 4 (BDL26LogicalDefectProtection.deltaX S 2 u q)=0 ∧
      BDL26LogicalDefectProtection.deltaX S 2 u q ∉ LinearMap.range
        (tannerCoboundary0 (state S 4).presentation) := by sorry
