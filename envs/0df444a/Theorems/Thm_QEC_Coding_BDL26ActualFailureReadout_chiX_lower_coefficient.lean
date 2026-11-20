-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ActualFailureReadout_chiX_lower_coefficient
-- name    : QEC.Coding.BDL26ActualFailureReadout.chiX_lower_coefficient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:35:00.324917+00:00
-- url     : https://prove2.me/theorems/747e1812-8d1e-405c-a4e1-a5ced41e13a5
-- title:
--   BDL26 Actual Failure Readout: chi X lower coefficient
-- statement:
--   The lower coefficient uses the SAME two correlated descents and base words.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/ActualFailureReadout.lean#L88-L94
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/ActualFailureReadout.lean#L88-L94

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

theorem QEC.Coding.BDL26ActualFailureReadout.chiX_lower_coefficient (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (a : (SuffixData S n).family.Cochain1 (TopIndex n))
    (ha : (SuffixData S n).family.coboundary1 (TopIndex n) a=(input S n u).val) :
    BDL26LogicalDefectProtection.chiX S n u q=
      lowerCoefficient S n (input S n u) (flip S n q) a ha := by sorry
