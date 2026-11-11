-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_lower_self
-- name    : QEC.Coding.BDL26RXPhysicalStarTransport.lower_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T14:03:56.119976+00:00
-- url     : https://prove2.me/theorems/2de7d854-320c-4672-9504-cc1c20cd685c
-- title:
--   BDL26 RXPhysical Star Transport: lower self
-- statement:
--   The BDL26 RXPhysical Star Transport construction uses the lower self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L335-L336
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L335-L336

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_lower_self
attribute [local simp] QEC.Coding.BDL26RXFiniteBlockTransport.lower_self


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXPhysicalStarTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport
open BDL26RXLocalReplacement BDL26ReplacementSupport MultiscaleDecoder
open RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXPhysicalStarTransport.lower_self (u : FamilyX S depth i.succ) (a : Upper S depth i) :
    L S depth i h u a a=0 := by sorry
