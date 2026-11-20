-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalSearchFailureReduction_second_returned_record
-- name    : QEC.Coding.BDL26LocalSearchFailureReduction.second_returned_record
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:11:06.089084+00:00
-- url     : https://prove2.me/theorems/75edeea2-5a42-4a4d-b259-8ad0419acb8d
-- title:
--   BDL26 Local Search Failure Reduction: second returned record
-- statement:
--   Complete actual SECOND returned record; neither its word nor its owner is replaced.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LocalSearchFailureReduction.lean#L169-L177
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LocalSearchFailureReduction.lean#L169-L177

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

theorem QEC.Coding.BDL26LocalSearchFailureReduction.second_returned_record (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (hb : localSuccess S (secondReadout S n u q)) :
    ∃ w : Word F (BDL26LevelTwoDecoder.ExecutableQ S),
      localSearch S (secondReadout S n u q)=some w ∧
      D S (secondReadout S n u q)=BDL26LevelTwoDecoder.toActualError S w ∧
      levelTwoLocalError S (D S (secondReadout S n u q)) ∧
      delta S (D S (secondReadout S n u q))=secondReadout S n u q := by sorry
