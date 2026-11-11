-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_correction_difference_supported
-- name    : QEC.Coding.BDL26RXPhysicalStarTransport.correction_difference_supported
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T14:27:40.205272+00:00
-- url     : https://prove2.me/theorems/2db0c1de-e9bd-4c5f-a2fd-9acd764032b7
-- title:
--   BDL26 RXPhysical Star Transport: correction difference supported
-- statement:
--   The BDL26 RXPhysical Star Transport construction uses the correction difference supported property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L214-L219
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L214-L219

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_correction_difference_supported
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_correction_difference_supported
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_correction_difference_supported

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

theorem QEC.Coding.BDL26RXPhysicalStarTransport.correction_difference_supported (u : FamilyX S depth i.succ) (a b : Upper S depth i)
    (he : Localized S depth i u a b) :
    hammingSupport ((run S depth i h a).correction+(run S depth i h b).correction) ⊆
      star1 S depth i h (parentX S depth i h u) := by sorry
