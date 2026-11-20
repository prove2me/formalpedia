-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPrimitiveC2QEndpoint_dualReadout_boundary
-- name    : QEC.Coding.BDL26RXPrimitiveC2QEndpoint.dualReadout_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T13:31:32.823384+00:00
-- url     : https://prove2.me/theorems/8f7245cd-0970-4097-b4f0-6109dc140cc2
-- title:
--   BDL26 RXPrimitive C2 QEndpoint: dual Readout boundary
-- statement:
--   No Z or Q potential summand is omitted from the boundary identity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveC2QEndpoint.lean#L1458-L1465
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveC2QEndpoint.lean#L1458-L1465

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveC2QEndpoint_LiteralPart1_QECert


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXPrimitiveC2QEndpoint
open MultiscaleDecoder BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26CSSHamiltonian BDL26ActualFailureReadout BDL26LevelTwoCode
open BDL26OwnerIncidenceMasks
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26LocalizedHistoryErrorDescent BDL26RZMap1CoordinateBridge
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder BDL26RXPhysicalCoordinateTrace
open scoped Classical BigOperators
attribute [local instance] QEC.Coding.BDL26RXPrimitiveC2QEndpoint.rawOneXEncodable
attribute [local instance] QEC.Coding.BDL26RXPrimitiveC2QEndpoint.rawOneQEncodable
attribute [local instance] QEC.Coding.BDL26RXPrimitiveC2QEndpoint.rawOneZEncodable
attribute [local instance] QEC.Coding.BDL26RXPrimitiveC2QEndpoint.executableTransposeFaceEncodable
attribute [local instance] QEC.Coding.BDL26RXPrimitiveC2QEndpoint.executableTransposeEdgeEncodable
attribute [local instance] QEC.Coding.BDL26RXPrimitiveC2QEndpoint.baseZeroX
attribute [local instance] QEC.Coding.BDL26RXPrimitiveC2QEndpoint.rawRX0Encodable
attribute [local instance] QEC.Coding.BDL26RXPrimitiveC2QEndpoint.rawRX1Encodable
attribute [local instance] QEC.Coding.BDL26RXPrimitiveC2QEndpoint.baseXEncodable
attribute [local instance] QEC.Coding.BDL26RXPrimitiveC2QEndpoint.baseQEncodable
attribute [local instance] QEC.Coding.BDL26RXPrimitiveC2QEndpoint.baseZEncodable
attribute [local instance] QEC.Coding.BDL26RXPrimitiveC2QEndpoint.baseFaceEncodable
attribute [local instance] QEC.Coding.BDL26RXPrimitiveC2QEndpoint.rawOneXEncodable QEC.Coding.BDL26RXPrimitiveC2QEndpoint.rawOneQEncodable QEC.Coding.BDL26RXPrimitiveC2QEndpoint.rawOneZEncodable QEC.Coding.BDL26RXPrimitiveC2QEndpoint.executableTransposeFaceEncodable QEC.Coding.BDL26RXPrimitiveC2QEndpoint.executableTransposeEdgeEncodable QEC.Coding.BDL26RXPrimitiveC2QEndpoint.baseZeroX QEC.Coding.BDL26RXPrimitiveC2QEndpoint.rawRX0Encodable QEC.Coding.BDL26RXPrimitiveC2QEndpoint.rawRX1Encodable QEC.Coding.BDL26RXPrimitiveC2QEndpoint.baseXEncodable QEC.Coding.BDL26RXPrimitiveC2QEndpoint.baseQEncodable QEC.Coding.BDL26RXPrimitiveC2QEndpoint.baseZEncodable QEC.Coding.BDL26RXPrimitiveC2QEndpoint.baseFaceEncodable

theorem QEC.Coding.BDL26RXPrimitiveC2QEndpoint.dualReadout_boundary (S : OddScale) (p : Word F (RawTwo S).X) :
    dualReadout S (tannerCoboundary0 (RawTwo S) p)=0 := by sorry
