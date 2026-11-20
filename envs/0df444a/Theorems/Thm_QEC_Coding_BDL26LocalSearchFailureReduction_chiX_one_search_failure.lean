-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalSearchFailureReduction_chiX_one_search_failure
-- name    : QEC.Coding.BDL26LocalSearchFailureReduction.chiX_one_search_failure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:08:54.954329+00:00
-- url     : https://prove2.me/theorems/69695011-9a5b-46a1-b74b-ed54b569ba0f
-- title:
--   BDL26 Local Search Failure Reduction: chi X one search failure
-- statement:
--   Unconditional necessary failure alternative for EVERY actual coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LocalSearchFailureReduction.lean#L265-L274
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LocalSearchFailureReduction.lean#L265-L274

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

theorem QEC.Coding.BDL26LocalSearchFailureReduction.chiX_one_search_failure (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (hc : BDL26LogicalDefectProtection.chiX S n u q=1) :
    firstReadout S n u≠0 ∨ localSearch S (secondReadout S n u q)=none := by sorry
