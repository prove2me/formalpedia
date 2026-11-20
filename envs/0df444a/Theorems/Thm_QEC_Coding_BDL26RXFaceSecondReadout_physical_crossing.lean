-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFaceSecondReadout_physical_crossing
-- name    : QEC.Coding.BDL26RXFaceSecondReadout.physical_crossing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:09:35.168851+00:00
-- url     : https://prove2.me/theorems/deda1740-3dfc-4bd6-b501-2374127cfd39
-- title:
--   BDL26 RXFace Second Readout: physical crossing
-- statement:
--   Physical crossing, retaining exactly the original input, perturbation and
--   FIRST/SECOND operations. The nonzero endpoint will be constructed below.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L200-L210
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L200-L210

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

theorem QEC.Coding.BDL26RXFaceSecondReadout.physical_crossing (S : OddScale) (n : Nat)
    (e : Word F (Physical S (n+2)))
    (hzero : physicalReadout S n 0=0) (hne : physicalReadout S n e≠0) :
    ∃ (a : Word F (Physical S (n+2))) (q : Physical S (n+2)),
      q∈hammingSupport e ∧ firstReadout S n (physicalInput S n a)=0 ∧
      secondReadout S n (physicalInput S n a) q≠0 := by sorry
