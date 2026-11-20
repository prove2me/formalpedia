-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalSearchFailureReduction_some_chiX_zero
-- name    : QEC.Coding.BDL26LocalSearchFailureReduction.some_chiX_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:09:56.639854+00:00
-- url     : https://prove2.me/theorems/7836e4f0-a2a8-47fa-a44c-878024747bce
-- title:
--   BDL26 Local Search Failure Reduction: some chi X zero
-- statement:
--   Public Option-valued version consumes the actual returned word.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LocalSearchFailureReduction.lean#L257-L262
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LocalSearchFailureReduction.lean#L257-L262

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroFaceEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LocalSearchFailureReduction
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalSearchFailureReduction
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder MultiscaleDecoder PauliSymplectic
open BDL26CSSHamiltonian BDL26ActualFailureReadout
open scoped Classical BigOperators

theorem QEC.Coding.BDL26LocalSearchFailureReduction.some_chiX_zero (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (hs : firstReadout S n u=0)
    (w : Word F (BDL26LevelTwoDecoder.ExecutableQ S))
    (hw : localSearch S (secondReadout S n u q)=some w) :
    BDL26LogicalDefectProtection.chiX S n u q=0 := by sorry
