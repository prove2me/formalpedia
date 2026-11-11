-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_updated_supported
-- name    : QEC.Coding.BDL26RXPhysicalStarTransport.updated_supported
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T14:34:25.164122+00:00
-- url     : https://prove2.me/theorems/d99efc09-e71b-480a-bd0a-37886e1684ce
-- title:
--   BDL26 RXPhysical Star Transport: updated supported
-- statement:
--   The BDL26 RXPhysical Star Transport construction uses the updated supported property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L221-L225
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L221-L225

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_updated_supported
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_updated_supported
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_updated_supported

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

theorem QEC.Coding.BDL26RXPhysicalStarTransport.updated_supported (u : FamilyX S depth i.succ) (a b : Upper S depth i)
    (he : Localized S depth i u a b) :
    hammingSupport (updated S depth i h a b) ⊆ star1 S depth i h (parentX S depth i h u) := by sorry
