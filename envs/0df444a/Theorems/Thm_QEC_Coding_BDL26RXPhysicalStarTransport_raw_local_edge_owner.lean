-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_raw_local_edge_owner
-- name    : QEC.Coding.BDL26RXPhysicalStarTransport.raw_local_edge_owner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:14:33.999658+00:00
-- url     : https://prove2.me/theorems/51d4b1e0-ea6f-4689-818d-0732f2f10fae
-- title:
--   BDL26 RXPhysical Star Transport: raw local edge owner
-- statement:
--   Materialized local edges retain their old X endpoint owner.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L58-L64
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L58-L64

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXPhysicalStarTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport
open BDL26RXLocalReplacement BDL26ReplacementSupport MultiscaleDecoder
open RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXPhysicalStarTransport.raw_local_edge_owner (P : TannerSquarePresentation) (S : OddScale)
    (u : RX0 P S) (e : Σ x : P.X, DoubleCylinderEdge P x S)
    (hu : rxXQIncidence P S u (Sum.inl e)=true) : u.1=e.1 := by sorry
