-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalSearchFailureReduction_first_zero_no_local_preimage
-- name    : QEC.Coding.BDL26LocalSearchFailureReduction.first_zero_no_local_preimage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:14:50.133219+00:00
-- url     : https://prove2.me/theorems/8e3af6bd-a33f-4e45-bdc7-e50711431700
-- title:
--   BDL26 Local Search Failure Reduction: first zero no local preimage
-- statement:
--   NONE excludes ALL owner-local representatives of the original SECOND syndrome.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LocalSearchFailureReduction.lean#L283-L288
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LocalSearchFailureReduction.lean#L283-L288

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroFaceEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LocalSearchFailureReduction
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalSearchFailureReduction
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder MultiscaleDecoder PauliSymplectic
open BDL26CSSHamiltonian BDL26ActualFailureReadout
open scoped Classical BigOperators

theorem QEC.Coding.BDL26LocalSearchFailureReduction.first_zero_no_local_preimage (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (hs : firstReadout S n u=0)
    (hc : BDL26LogicalDefectProtection.chiX S n u q=1) :
    ¬∃ e : Error S, levelTwoLocalError S e ∧ delta S e=secondReadout S n u q := by sorry
