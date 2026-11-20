-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HigherRXFaceTower_full_potential_formula
-- name    : QEC.Coding.BDL26HigherRXFaceTower.full_potential_formula
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:12:19.231048+00:00
-- url     : https://prove2.me/theorems/b92fa511-4dae-49de-9591-bd52f22131b4
-- title:
--   BDL26 Higher RXFace Tower: full potential formula
-- statement:
--   The BDL26 Higher RXFace Tower construction uses the full potential formula property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/HigherRXFaceTower.lean#L509-L513
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/HigherRXFaceTower.lean#L509-L513

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroQVertexTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundaryTailInvariance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_HigherRXFaceTower
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HigherRXFaceTower
open MultiscaleDecoder BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26LocalizedHistoryErrorDescent BDL26RZMap1CoordinateBridge
open BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26CSSHamiltonian BDL26ActualFailureReadout BDL26TransposedStoppedDecoder
open PauliSymplectic
open scoped Classical BigOperators

theorem QEC.Coding.BDL26HigherRXFaceTower.full_potential_formula (S : OddScale) (n : Nat) (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Family S n q) :
    fullPotential S n u q t=
      intervalMap0 (SuffixData S n) 0 (TopIndex n) (Nat.zero_le _)
        (bottomPotential S n u q t)+BDL26ActualFailureReadout.accumulated S n u q := by sorry
