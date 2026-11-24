-- Prove2me | Theorems.Thm_Set_PairwiseDisjoint_injOn
-- name    : Set.PairwiseDisjoint.injOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:50:09.671624+00:00
-- url     : https://prove2.me/theorems/479b9a51-d97e-4108-b356-f5f180adb901
-- title:
--   Pairwise Disjoint: inj On
-- statement:
--   A pairwise disjoint family of nonzero elements is injective on its index set.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Sensitivity.lean#L38-L44
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Sensitivity.lean#L38-L44

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
set_option autoImplicit true
@[expose] public section
public section

theorem Set.PairwiseDisjoint.injOn {ι α : Type*} [Lattice α] [OrderBot α] {f : ι → α}
    {s : Set ι} (h : s.PairwiseDisjoint f) (hne : ∀ i ∈ s, f i ≠ ⊥) : s.InjOn f := by sorry
