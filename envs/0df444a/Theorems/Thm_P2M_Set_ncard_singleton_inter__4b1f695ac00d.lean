-- Prove2me | Theorems.Thm_P2M_Set_ncard_singleton_inter__4b1f695ac00d
-- name    : P2M_Set_ncard_singleton_inter__4b1f695ac00d
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:30:42.643332+00:00
-- url     : https://prove2.me/theorems/de48f56e-d02c-4687-a5ba-9d617aa540fd
-- title:
--   P2 M Set ncard singleton inter  4b1f695ac00d: P2 M Set ncard singleton inter  4b1f695ac00d
-- statement:
--   The P2 M Set ncard singleton inter  4b1f695ac00d construction uses the P2 M Set ncard singleton inter  4b1f695ac00d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Data/Set/Card.lean#L25-L27
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Data/Set/Card.lean#L25-L27

module
public import Mathlib.Data.Set.Card
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Data_Set_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Data_Set_Card
set_option autoImplicit true
@[expose] public section
public section
open Set
variable {α : Type*}

theorem P2M_Set_ncard_singleton_inter__4b1f695ac00d (a : α) (s : Set α) [Decidable (a ∈ s)] :
    ({a} ∩ s).ncard = if a ∈ s then 1 else 0 := by sorry

alias «Set».«ncard_singleton_inter'» := P2M_Set_ncard_singleton_inter__4b1f695ac00d
