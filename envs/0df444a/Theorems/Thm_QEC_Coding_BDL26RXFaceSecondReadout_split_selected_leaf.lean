-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFaceSecondReadout_split_selected_leaf
-- name    : QEC.Coding.BDL26RXFaceSecondReadout.split_selected_leaf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:10:36.159178+00:00
-- url     : https://prove2.me/theorems/3b78f11a-5e43-4f17-9470-704572e522da
-- title:
--   BDL26 RXFace Second Readout: split selected leaf
-- statement:
--   At every incident Q cylinder, all its selected leaf values are the same
--   original root coefficient plus the prescribed Z bit. This retains all ties.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L721-L737
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L721-L737

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

theorem QEC.Coding.BDL26RXFaceSecondReadout.split_selected_leaf (x : P.X) (q : P.Q) (hxq : P.xq x q=true)
    (z : QStarEdge P q) (c : BDL26FiniteTannerSquare.Two) :
    selectedQWord (gradientInput x (splitPotential x)) q (c,Sum.inl (Sum.inr z))=
      rootWord x q+zCopyBit z.1 := by sorry
