-- Prove2me | Theorems.Thm_QEC_Coding_BDL26EvenC4SingleCoordinateLift_deltaX_embedC3Input
-- name    : QEC.Coding.BDL26EvenC4SingleCoordinateLift.deltaX_embedC3Input
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:46:38.997449+00:00
-- url     : https://prove2.me/theorems/55f3bf66-3b2d-4eb2-968b-75ff39458bc7
-- title:
--   BDL26 Even C4 Single Coordinate Lift: delta X embed C3 Input
-- statement:
--   The full original two-history residual, including BOTH original base calls
--   and BOTH actual top RZ corrections, differs by an actual full upper boundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/EvenC4SingleCoordinateLift.lean#L532-L566
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/EvenC4SingleCoordinateLift.lean#L532-L566

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_ActualFailureReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_EvenC4SingleCoordinateLift
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26EvenC4SingleCoordinateLift
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26AlternatingCochain BDL26OwnerIncidenceMasks
open BDL26TransposedStoppedDecoder BDL26CSSHamiltonian
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26HistoryLogicalResidual BDL26ActualFailureReadout
open BDL26RZMap1CoordinateBridge
open RXCoarseGraining RXCoarseGrainingData
open scoped Classical

theorem QEC.Coding.BDL26EvenC4SingleCoordinateLift.deltaX_embedC3Input (S : OddScale) (u : XSyndromeDomain S 1)
    (q : Physical S 3)
    (v : BDL26TannerLocalRegularity.QDoubleCylinderVertex (transposePresentation (state S 3).presentation) q S) :
    ∃ p : Word F (state S 4).presentation.X,
      BDL26LogicalDefectProtection.deltaX S 2 (embedC3Input S u) (rzOldQCoordinate S q v)=
        stepMap1 S 3 (BDL26LogicalDefectProtection.deltaX S 1 u q)+
          tannerCoboundary0 (state S 4).presentation p := by sorry
