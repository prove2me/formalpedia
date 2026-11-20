-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFaceSecondReadout_nonzero_second_returned
-- name    : QEC.Coding.BDL26RXFaceSecondReadout.nonzero_second_returned
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:11:16.608466+00:00
-- url     : https://prove2.me/theorems/014c8583-f4ab-430d-a3ed-944d4737f581
-- title:
--   BDL26 RXFace Second Readout: nonzero second returned
-- statement:
--   The nonzero SECOND has an independently returned original search word and
--   an actually nonzero correction. Nonzeroness follows from the original syndrome
--   equation; it is not stored as a premise of a witness structure.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L1025-L1039
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L1025-L1039

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXFaceEdgeTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXFaceSecondReadout
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXFaceSecondReadout
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder MultiscaleDecoder PauliSymplectic
open BDL26CSSHamiltonian BDL26ActualFailureReadout BDL26RXDecoderAdapter
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXFaceSecondReadout.nonzero_second_returned (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : BDL26RXFaceEdgeTower.Tower S n q)
    (hfirst : firstReadout S n u=0) (hsecond : secondReadout S n u q≠0) :
    ∃ w : Word F (BDL26LevelTwoDecoder.ExecutableQ S),
      BDL26LevelTwoLocalBranchEndpoint.localSearch S (secondReadout S n u q)=some w ∧
      BDL26RXFaceEdgeTower.D S (secondReadout S n u q)=BDL26LevelTwoDecoder.toActualError S w ∧
      levelTwoLocalError S (BDL26RXFaceEdgeTower.D S (secondReadout S n u q)) ∧
      BDL26RXFaceEdgeTower.delta S (BDL26RXFaceEdgeTower.D S (secondReadout S n u q))=
        secondReadout S n u q ∧
      BDL26RXFaceEdgeTower.D S (secondReadout S n u q)≠0 := by sorry
