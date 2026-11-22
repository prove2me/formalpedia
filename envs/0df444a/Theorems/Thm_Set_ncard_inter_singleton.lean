-- Prove2me | Theorems.Thm_Set_ncard_inter_singleton
-- name    : Set.ncard_inter_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:26:48.129374+00:00
-- url     : https://prove2.me/theorems/a42248d3-a974-4a37-a4db-867953b90b2e
-- title:
--   Set: ncard inter singleton
-- statement:
--   The Set construction uses the ncard inter singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Data/Set/Card.lean#L29-L31
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Data/Set/Card.lean#L29-L31

module
public import Mathlib.Data.Set.Card
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Data_Set_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Data_Set_Card
set_option autoImplicit true
@[expose] public section
public section
open Set
variable {α : Type*}

theorem Set.ncard_inter_singleton (a : α) (s : Set α) [Decidable (a ∈ s)] :
    (s ∩ {a}).ncard = if a ∈ s then 1 else 0 := by sorry
