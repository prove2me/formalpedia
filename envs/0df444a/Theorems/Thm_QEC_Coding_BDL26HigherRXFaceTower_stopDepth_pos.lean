-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HigherRXFaceTower_stopDepth_pos
-- name    : QEC.Coding.BDL26HigherRXFaceTower.stopDepth_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:12:16.704723+00:00
-- url     : https://prove2.me/theorems/ccf6910c-f8dc-4fde-86f2-7a66c153da8a
-- title:
--   BDL26 Higher RXFace Tower: stop Depth pos
-- statement:
--   The BDL26 Higher RXFace Tower construction uses the stop Depth pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/HigherRXFaceTower.lean#L63-L68
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/HigherRXFaceTower.lean#L63-L68

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

theorem QEC.Coding.BDL26HigherRXFaceTower.stopDepth_pos {S : OddScale} {n : Nat} {q : Physical S (n+2)}
    (t : Family S n q) : 1 ≤ stopDepth t := by sorry
