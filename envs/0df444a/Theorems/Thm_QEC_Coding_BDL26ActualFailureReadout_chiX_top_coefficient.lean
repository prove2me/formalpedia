-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ActualFailureReadout_chiX_top_coefficient
-- name    : QEC.Coding.BDL26ActualFailureReadout.chiX_top_coefficient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:32:23.964179+00:00
-- url     : https://prove2.me/theorems/8d2a2779-d32e-4299-8f99-d0c6f1f45809
-- title:
--   BDL26 Actual Failure Readout: chi X top coefficient
-- statement:
--   Actual chiX is the canonical coefficient of the FULL original top word.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/ActualFailureReadout.lean#L75-L85
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/ActualFailureReadout.lean#L75-L85

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalizedHistoryErrorDescent
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoLocalBranchEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoOldXStarEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_ActualFailureReadout
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26ActualFailureReadout
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder MultiscaleDecoder PauliSymplectic
open BDL26CSSHamiltonian
open scoped Classical BigOperators

theorem QEC.Coding.BDL26ActualFailureReadout.chiX_top_coefficient (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) :
    BDL26LogicalDefectProtection.chiX S n u q=
      topCoefficient S n (input S n u) (flip S n q) := by sorry
