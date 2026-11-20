-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalSearchFailureReduction_rawStarPotential_spec
-- name    : QEC.Coding.BDL26LocalSearchFailureReduction.rawStarPotential_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:10:44.540764+00:00
-- url     : https://prove2.me/theorems/42515598-bfeb-4f57-9dcb-43dc954f260e
-- title:
--   BDL26 Local Search Failure Reduction: raw Star Potential spec
-- statement:
--   The BDL26 Local Search Failure Reduction construction uses the raw Star Potential spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LocalSearchFailureReduction.lean#L131-L135
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LocalSearchFailureReduction.lean#L131-L135

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

theorem QEC.Coding.BDL26LocalSearchFailureReduction.rawStarPotential_spec (S : OddScale) (x : (C S).X) (h : Error S)
    (hh : hammingSupport h ⊆ BDL26RXPhysicalStarTransport.physicalXStar (C S) x)
    (hb : localSuccess S (delta S h)) :
    boundary S (rawStarPotential S x h hh hb)=h+D S 0+D S (delta S h) := by sorry
