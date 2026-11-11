-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_local_edge_parent_none
-- name    : QEC.Coding.BDL26RZPhysicalStarTransport.local_edge_parent_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:41:07.538306+00:00
-- url     : https://prove2.me/theorems/0e22f73f-d41a-4a83-b61d-34321552600d
-- title:
--   BDL26 RZPhysical Star Transport: local edge parent none
-- statement:
--   The BDL26 RZPhysical Star Transport construction uses the local edge parent none property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalStarTransport.lean#L227-L232
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalStarTransport.lean#L227-L232

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZPhysicalStarTransport
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26DecodingGraph BDL26IndexedDecoder BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementSupport BDL26ReplacementCochainMaps
open BDL26RZDecoderAdapter BDL26RZErrorPullback MultiscaleDecoder
open RZCoarseGraining RZCoarseGrainingData
open BDL26RZFiniteBlockTransport
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (odd : ¬i.val%2=0)

theorem QEC.Coding.BDL26RZPhysicalStarTransport.local_edge_parent_none (z : (Old S depth i).Z)
    (e : ZDoubleCylinderEdge (Old S depth i) z S) :
    parent S (i.val+1) (Vertex.q (upperQChart S depth i odd (.inl ⟨z,e⟩)))=none := by sorry
