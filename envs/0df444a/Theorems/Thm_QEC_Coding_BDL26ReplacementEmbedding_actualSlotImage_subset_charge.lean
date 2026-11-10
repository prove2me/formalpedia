-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_actualSlotImage_subset_charge
-- name    : QEC.Coding.BDL26ReplacementEmbedding.actualSlotImage_subset_charge
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:36:40.134785+00:00
-- url     : https://prove2.me/theorems/058ff0cb-94e6-4cd6-94da-3d9adc795a75
-- title:
--   BDL26 Replacement Embedding: actual Slot Image subset charge
-- statement:
--   The already proved local geometric containments cover every actual slot.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1770-L1792
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1770-L1792

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
noncomputable section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem QEC.Coding.BDL26ReplacementEmbedding.actualSlotImage_subset_charge (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (slot : PatchSlot S) :
    rxFaceImage P S J ((rxFaceSlotEquiv P S).symm (f, slot)) ⊆
      rxFaceImage P S J ((rxFaceSlotEquiv P S).symm (f, chargePatchSlot S slot)) := by sorry
