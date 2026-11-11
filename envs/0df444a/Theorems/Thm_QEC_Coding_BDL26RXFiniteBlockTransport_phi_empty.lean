-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_phi_empty
-- name    : QEC.Coding.BDL26RXFiniteBlockTransport.phi_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:57:46.686471+00:00
-- url     : https://prove2.me/theorems/7d28007b-7769-4f77-8998-679940c56839
-- title:
--   BDL26 RXFinite Block Transport: phi empty
-- statement:
--   The BDL26 RXFinite Block Transport construction uses the phi empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L560-L560
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L560-L560

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXFiniteBlockTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXFiniteBlockTransport.phi_empty (a b : Upper S depth i) : Phi S depth i h ∅ a b=0 := by sorry
