-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFaceSecondReadout_gradientInput_root_forced
-- name    : QEC.Coding.BDL26RXFaceSecondReadout.gradientInput_root_forced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:07:31.276199+00:00
-- url     : https://prove2.me/theorems/1d769cda-034d-487f-90eb-b1bcfd4d0b0c
-- title:
--   BDL26 RXFace Second Readout: gradient Input root forced
-- statement:
--   The previously proved budget now applies to the ACTUAL original selector,
--   with its cleaned input computed from the physical local gradient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L665-L672
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L665-L672

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

theorem QEC.Coding.BDL26RXFaceSecondReadout.gradientInput_root_forced (x : P.X)
    (g : Word F (DoubleCylinderVertex P x witnessScale)) (q : P.Q)
    (hxq : P.xq x q=true) (b : F)
    (hg : rxXQDegreeZero P (state witnessScale 2).admissible.toTannerSquareAdmissible
      q x hxq witnessScale g=qPortWord P q b) :
    selectedQWord (gradientInput x g) q (0,Sum.inl (Sum.inl ()))=b := by sorry
