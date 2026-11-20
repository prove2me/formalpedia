-- Prove2me | Theorems.Thm_QEC_Coding_BDL26EvenC4SingleCoordinateLift_chiX_embedC3Input
-- name    : QEC.Coding.BDL26EvenC4SingleCoordinateLift.chiX_embedC3Input
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:47:33.533898+00:00
-- url     : https://prove2.me/theorems/71c46cf7-6aff-4460-adf3-de6f5866997a
-- title:
--   BDL26 Even C4 Single Coordinate Lift: chi X embed C3 Input
-- statement:
--   The actual canonical H1 defect coefficient of one physical old-Q lift is
--   exactly its actual C3 coefficient, for every legal background and OddScale.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/EvenC4SingleCoordinateLift.lean#L570-L606
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/EvenC4SingleCoordinateLift.lean#L570-L606

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

theorem QEC.Coding.BDL26EvenC4SingleCoordinateLift.chiX_embedC3Input (S : OddScale) (u : XSyndromeDomain S 1)
    (q : Physical S 3)
    (v : BDL26TannerLocalRegularity.QDoubleCylinderVertex (transposePresentation (state S 3).presentation) q S) :
    BDL26LogicalDefectProtection.chiX S 2 (embedC3Input S u) (rzOldQCoordinate S q v)=
      BDL26LogicalDefectProtection.chiX S 1 u q := by sorry
