-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPhysicalCoordinateTrace_primitive_positive
-- name    : QEC.Coding.BDL26RXPhysicalCoordinateTrace.primitive_positive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:07:07.218362+00:00
-- url     : https://prove2.me/theorems/96a7613b-8ae3-4876-86ca-c697c0d304b0
-- title:
--   BDL26 RXPhysical Coordinate Trace: primitive positive
-- statement:
--   The BDL26 RXPhysical Coordinate Trace construction uses the primitive positive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPhysicalCoordinateTrace.lean#L122-L125
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPhysicalCoordinateTrace.lean#L122-L125

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXQEdgePairTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXFaceEdgeTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPhysicalCoordinateTrace
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXPhysicalCoordinateTrace
open MultiscaleDecoder BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26CSSHamiltonian BDL26ActualFailureReadout
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26HistorySyndromeSensitivity BDL26TannerLocalRegularity
open scoped Classical

theorem QEC.Coding.BDL26RXPhysicalCoordinateTrace.primitive_positive {S : OddScale} {b : Nat} (p : Primitive S b) : 1≤b := by sorry
