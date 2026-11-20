-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalSearchFailureReduction_original_correction_equation
-- name    : QEC.Coding.BDL26LocalSearchFailureReduction.original_correction_equation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:22:52.223926+00:00
-- url     : https://prove2.me/theorems/709f1f8d-4c63-4cec-aa29-148e79990e83
-- title:
--   BDL26 Local Search Failure Reduction: original correction equation
-- statement:
--   The BDL26 Local Search Failure Reduction construction uses the original correction equation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LocalSearchFailureReduction.lean#L236-L243
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LocalSearchFailureReduction.lean#L236-L243

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroFaceEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LocalSearchFailureReduction
import Theorems.Thm_QEC_Coding_BDL26FirstZeroFaceEndpoint_original_correction_equation

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

theorem QEC.Coding.BDL26LocalSearchFailureReduction.original_correction_equation (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (hs : firstReadout S n u=0)
    (hb : localSuccess S (secondReadout S n u q)) :
    (SuffixData S n).family.coboundary0 (TopIndex n) (fullPotential S n u q hs hb)=
      flip S n q+xCorrection S n u+xCorrection S n (translateX S n u (flip S n q)) := by sorry
