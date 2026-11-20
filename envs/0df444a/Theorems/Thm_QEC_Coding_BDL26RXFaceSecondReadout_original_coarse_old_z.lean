-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFaceSecondReadout_original_coarse_old_z
-- name    : QEC.Coding.BDL26RXFaceSecondReadout.original_coarse_old_z
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:03:44.405087+00:00
-- url     : https://prove2.me/theorems/5c8b6d4e-a2e8-45fb-a4b7-7e0805b529d0
-- title:
--   BDL26 RXFace Second Readout: original coarse old z
-- statement:
--   The original coarse coordinate is doubled-Z COPY ZERO, retaining all
--   selected Q components. This is not the parity of the two physical copies.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L551-L585
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L551-L585

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

theorem QEC.Coding.BDL26RXFaceSecondReadout.original_coarse_old_z (sigma : Syn) (z : P.Z)
    (hx : ∀ x, restrictWordLinear (Lx.syndromeRegion x) sigma.val=0) :
    (BDL26RXDecoderAdapter.rxStepOutput witnessScale 3 rxIndex rxIndex_even sigma).coarse.val z=
      sigma.val (Sum.inr (z,0))+
        ∑ q : P.Q,BDL26RXDecoderAdapter.qFlow P witnessScale q (selectedQWord sigma q)
          (Sum.inr (z,0)) := by sorry
