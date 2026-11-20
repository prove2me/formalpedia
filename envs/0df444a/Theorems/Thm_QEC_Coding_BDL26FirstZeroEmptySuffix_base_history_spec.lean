-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FirstZeroEmptySuffix_base_history_spec
-- name    : QEC.Coding.BDL26FirstZeroEmptySuffix.base_history_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:55:55.77003+00:00
-- url     : https://prove2.me/theorems/5af85788-6d9c-4774-8a3d-150dcbc65838
-- title:
--   BDL26 First Zero Empty Suffix: base history spec
-- statement:
--   Both stored original base calls occur in the full actual endpoint equation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/FirstZeroEmptySuffix.lean#L125-L151
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/FirstZeroEmptySuffix.lean#L125-L151

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroFaceEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroEmptySuffix
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

theorem QEC.Coding.BDL26FirstZeroEmptySuffix.base_history_spec (S : OddScale) (u : XSyndromeDomain S 0) (q : Physical S 2)
    (hs : firstReadout S 0 u=0) :
    (SuffixData S 0).family.coboundary0 0 (elementaryPotential S q)=
      (descent S 0 u q).word+
        (actualBase S 0).decode (actualInputs S 0 (input S 0 u) 0)+
        (actualBase S 0).decode
          (actualInputs S 0 (perturbTop S 0 (input S 0 u) (flip S 0 q)) 0) := by sorry
