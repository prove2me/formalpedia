-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_physicalQ_basis
-- name    : QEC.Coding.BDL26RZPhysicalStarTransport.physicalQ_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:38:35.875756+00:00
-- url     : https://prove2.me/theorems/9c8ab94b-b0d7-4648-97b6-e3d9acded8a0
-- title:
--   BDL26 RZPhysical Star Transport: physical Q basis
-- statement:
--   The physical global BDL26FiniteTannerSquare.Field basis equals the original chart-reindexed basis.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalStarTransport.lean#L365-L370
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalStarTransport.lean#L365-L370

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

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

theorem QEC.Coding.BDL26RZPhysicalStarTransport.physicalQ_basis (q : (Old S depth i).Q)
    (v : QDoubleCylinderVertex (transposePresentation (Old S depth i)) q S) :
    (read1 S depth i odd).symm (canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) (Sum.inr ⟨q,v⟩))=
      canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) (physicalQ S depth i odd q v) := by sorry
