-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ActualFailureReadout_first_base_original_D
-- name    : QEC.Coding.BDL26ActualFailureReadout.first_base_original_D
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:32:43.002575+00:00
-- url     : https://prove2.me/theorems/9a154735-f56f-421e-bf51-7a0d05cef341
-- title:
--   BDL26 Actual Failure Readout: first base original D
-- statement:
--   The stored base calls use the unchanged executable decoder D on both values.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/ActualFailureReadout.lean#L293-L295
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/ActualFailureReadout.lean#L293-L295

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

theorem QEC.Coding.BDL26ActualFailureReadout.first_base_original_D (S : OddScale) (n : Nat) (u : XSyndromeDomain S n) :
    (actualBase S n).decode (actualInputs S n (input S n u) 0)=
      BDL26LevelTwoDecoder.decode S (firstReadout S n u) := by sorry
