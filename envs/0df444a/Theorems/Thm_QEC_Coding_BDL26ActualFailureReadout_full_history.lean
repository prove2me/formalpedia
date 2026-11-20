-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ActualFailureReadout_full_history
-- name    : QEC.Coding.BDL26ActualFailureReadout.full_history
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:33:25.899882+00:00
-- url     : https://prove2.me/theorems/111986a9-7795-442c-9b32-144210c4d1b3
-- title:
--   BDL26 Actual Failure Readout: full history
-- statement:
--   Complete two-history equation before either C2 word is proved zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/ActualFailureReadout.lean#L348-L361
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/ActualFailureReadout.lean#L348-L361

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

theorem QEC.Coding.BDL26ActualFailureReadout.full_history (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) :
    BDL26LogicalDefectProtection.deltaX S n u q=
      intervalMap1 (SuffixData S n) 0 (TopIndex n) (Nat.zero_le _)
        ((descent S n u q).word+
          (actualBase S n).decode (actualInputs S n (input S n u) 0)+
          (actualBase S n).decode
            (actualInputs S n (perturbTop S n (input S n u) (flip S n q)) 0))+
      (SuffixData S n).family.coboundary0 (TopIndex n) (accumulated S n u q) := by sorry
