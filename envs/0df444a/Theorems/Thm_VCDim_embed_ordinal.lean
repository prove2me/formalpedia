-- Prove2me | Theorems.Thm_VCDim_embed_ordinal
-- name    : VCDim_embed_ordinal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:38:58.770651+00:00
-- url     : https://prove2.me/theorems/088a8fee-3368-4587-9658-1e9b5ac13086
-- title:
--   VCDim embed ordinal: VCDim embed ordinal
-- statement:
--   Embedding: finite VCDim embeds into OrdinalVCDim.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Ordinal.lean#L78-L106
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Ordinal.lean#L78-L106

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Littlestone
public import Mathlib.SetTheory.Ordinal.Basic
public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Data.EReal.Inv
public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.MetricSpace.Bounded
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Ordinal
set_option autoImplicit true
@[expose] public section
public section
universe u v

theorem VCDim_embed_ordinal (X : Type u) (C : ConceptClass X Bool)
    (n : ℕ) (h : VCDim X C = n) : OrdinalVCDim X C = (n : Ordinal) := by sorry
