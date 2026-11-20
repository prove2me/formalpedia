-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPrimitiveC2QEndpoint_global_cone_zero
-- name    : QEC.Coding.BDL26RXPrimitiveC2QEndpoint.global_cone_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T13:07:01.771914+00:00
-- url     : https://prove2.me/theorems/8c1033cb-eb5c-4f25-9294-e47f80f43dec
-- title:
--   BDL26 RXPrimitive C2 QEndpoint: global cone zero
-- statement:
--   A genuine Q-cone is forced to zero by the original global lookup order.
--   The lowering kernel is the full actual Q-edge coboundary, including its Z bits.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveC2QEndpoint.lean#L2086-L2112
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveC2QEndpoint.lean#L2086-L2112

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

theorem QEC.Coding.BDL26RXPrimitiveC2QEndpoint.global_cone_zero (S : OddScale) (a : Word F (levelTwoPresentation S).Q)
    (r : (RawOne S).Q) (x : (RawOne S).X) (hx : (RawOne S).xq x r=true)
    (c : BDL26FiniteTannerSquare.Two) :
    BDL26GlobalLookupLinearity.actualGlobal S
      (tannerCoboundary1 (levelTwoPresentation S) a)
      (.inr ⟨r,(c,.inl (.inl ()))⟩)=0 := by sorry
