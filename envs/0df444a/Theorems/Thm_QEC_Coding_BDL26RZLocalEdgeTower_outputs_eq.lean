-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZLocalEdgeTower_outputs_eq
-- name    : QEC.Coding.BDL26RZLocalEdgeTower.outputs_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:15:19.238384+00:00
-- url     : https://prove2.me/theorems/0f144c73-de16-4d26-af77-f290c74455d9
-- title:
--   BDL26 RZLocal Edge Tower: outputs eq
-- statement:
--   The BDL26 RZLocal Edge Tower construction uses the outputs eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RZLocalEdgeTower.lean#L403-L410
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RZLocalEdgeTower.lean#L403-L410

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroQVertexTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundaryTailInvariance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RZLocalEdgeTower
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZLocalEdgeTower
open MultiscaleDecoder BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26LocalizedHistoryErrorDescent BDL26RZMap1CoordinateBridge
open BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26CSSHamiltonian BDL26ActualFailureReadout BDL26TransposedStoppedDecoder
open PauliSymplectic
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RZLocalEdgeTower.outputs_eq (S : OddScale) (n : Nat) (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Killed S n q) (i : StepIndex n)
    (hi : i.succ.val ≤ seedDepth t) :
    actualOutput S n (input S n u) i=
      actualOutput S n (perturbTop S n (input S n u) (BDL26ActualFailureReadout.flip S n q)) i := by sorry
