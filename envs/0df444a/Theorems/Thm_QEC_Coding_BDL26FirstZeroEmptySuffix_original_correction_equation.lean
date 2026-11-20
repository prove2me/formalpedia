-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FirstZeroEmptySuffix_original_correction_equation
-- name    : QEC.Coding.BDL26FirstZeroEmptySuffix.original_correction_equation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:25:04.425976+00:00
-- url     : https://prove2.me/theorems/3be8867b-a7fb-42d9-ad4a-f073aa5883b8
-- title:
--   BDL26 First Zero Empty Suffix: original correction equation
-- statement:
--   The original input and its original translated input retain both corrections.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/FirstZeroEmptySuffix.lean#L169-L175
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/FirstZeroEmptySuffix.lean#L169-L175

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroFaceEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroEmptySuffix
import Theorems.Thm_QEC_Coding_BDL26FirstZeroFaceEndpoint_original_correction_equation

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FirstZeroEmptySuffix
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder MultiscaleDecoder PauliSymplectic
open BDL26CSSHamiltonian BDL26ActualFailureReadout
open scoped Classical BigOperators

theorem QEC.Coding.BDL26FirstZeroEmptySuffix.original_correction_equation (S : OddScale) (u : XSyndromeDomain S 0) (q : Physical S 2)
    (hs : firstReadout S 0 u=0) :
    (SuffixData S 0).family.coboundary0 (TopIndex 0) (fullPotential S u q)=
      flip S 0 q+xCorrection S 0 u+xCorrection S 0 (translateX S 0 u (flip S 0 q)) := by sorry
