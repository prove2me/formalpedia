-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FirstZeroEmptySuffix_base_potential_spec
-- name    : QEC.Coding.BDL26FirstZeroEmptySuffix.base_potential_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:57:31.903989+00:00
-- url     : https://prove2.me/theorems/b9823af6-9116-4f43-bde1-9d6cac186dc3
-- title:
--   BDL26 First Zero Empty Suffix: base potential spec
-- statement:
--   The BDL26 First Zero Empty Suffix construction uses the base potential spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/FirstZeroEmptySuffix.lean#L75-L78
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/FirstZeroEmptySuffix.lean#L75-L78

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

theorem QEC.Coding.BDL26FirstZeroEmptySuffix.base_potential_spec (S : OddScale) (q : Physical S 2) :
    boundary S (elementaryPotential S q)=
      physicalWord S q+D S 0+D S (delta S (flip S 0 q)) := by sorry
