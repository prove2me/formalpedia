-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFaceSecondReadout_exists_first_zero_second_nonzero
-- name    : QEC.Coding.BDL26RXFaceSecondReadout.exists_first_zero_second_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:10:46.083304+00:00
-- url     : https://prove2.me/theorems/029dd596-2c11-4213-9105-66f608b2a8ab
-- title:
--   BDL26 RXFace Second Readout: exists first zero second nonzero
-- statement:
--   Actual existential readout classification. The witness has the same
--   original fixed n=1 throughout. Its input is built from a physical prefix; the
--   next flip is a literal original face-edge seed, and SECOND is the unchanged
--   original readout after that physical translation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L1008-L1019
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L1008-L1019

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

theorem QEC.Coding.BDL26RXFaceSecondReadout.exists_first_zero_second_nonzero :
    ∃ (S : OddScale) (n : Nat) (u : XSyndromeDomain S n) (q : Physical S (n+2)),
      Nonempty (BDL26RXFaceEdgeTower.Tower S n q) ∧
      firstReadout S n u=0 ∧ secondReadout S n u q≠0 := by sorry
