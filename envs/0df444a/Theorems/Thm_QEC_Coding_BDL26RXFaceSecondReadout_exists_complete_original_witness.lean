-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFaceSecondReadout_exists_complete_original_witness
-- name    : QEC.Coding.BDL26RXFaceSecondReadout.exists_complete_original_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:12:13.866207+00:00
-- url     : https://prove2.me/theorems/4a687bcc-c35c-46ca-ae3b-42398eda0bcc
-- title:
--   BDL26 RXFace Second Readout: exists complete original witness
-- statement:
--   Whole actual witness consumer: original FIRST and SECOND, returned search
--   word, nonzero selected correction, BOTH literal base calls, and the full Phi
--   formula and original top correction equation all share the same S,n,u,q.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L1044-L1071
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L1044-L1071

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

theorem QEC.Coding.BDL26RXFaceSecondReadout.exists_complete_original_witness :
    ∃ (S : OddScale) (n : Nat) (u : XSyndromeDomain S n) (q : Physical S (n+2))
      (t : BDL26RXFaceEdgeTower.Tower S n q)
      (w : Word F (BDL26LevelTwoDecoder.ExecutableQ S)),
      firstReadout S n u=0 ∧ secondReadout S n u q≠0 ∧
      BDL26LevelTwoLocalBranchEndpoint.localSearch S (secondReadout S n u q)=some w ∧
      BDL26RXFaceEdgeTower.D S (secondReadout S n u q)=BDL26LevelTwoDecoder.toActualError S w ∧
      levelTwoLocalError S (BDL26RXFaceEdgeTower.D S (secondReadout S n u q)) ∧
      BDL26RXFaceEdgeTower.delta S (BDL26RXFaceEdgeTower.D S (secondReadout S n u q))=
        secondReadout S n u q ∧
      BDL26RXFaceEdgeTower.D S (secondReadout S n u q)≠0 ∧
      (SuffixData S n).family.coboundary0 0 (BDL26RXFaceEdgeTower.basePotential S n u q t)=
        (descent S n u q).word+
          (actualBase S n).decode (actualInputs S n (input S n u) 0)+
          (actualBase S n).decode
            (actualInputs S n (perturbTop S n (input S n u) (BDL26ActualFailureReadout.flip S n q)) 0) ∧
      BDL26RXFaceEdgeTower.fullPotential S n u q t=
        intervalMap0 (SuffixData S n) 0 (TopIndex n) (Nat.zero_le _)
          (BDL26RXFaceEdgeTower.basePotential S n u q t)+accumulated S n u q ∧
      (SuffixData S n).family.coboundary0 (TopIndex n)
        (BDL26RXFaceEdgeTower.fullPotential S n u q t)=
        BDL26ActualFailureReadout.flip S n q+xCorrection S n u+xCorrection S n (translateX S n u (BDL26ActualFailureReadout.flip S n q)) := by sorry
