-- Prove2me | Theorems.Thm_Parikh_LinearComponent_isLinearSet
-- name    : Parikh.LinearComponent.isLinearSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:57:05.30663+00:00
-- url     : https://prove2.me/theorems/408dc070-f8d2-4857-980c-d1172ed4af96
-- title:
--   Linear Component: is Linear Set
-- statement:
--   Each component denotes a linear set in Mathlib's sense.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Api.lean#L58-L59
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Api.lean#L58-L59

module
public import Definitions.Def_LeanPool_Parikh_ExecutableCompiler
public import Mathlib.Computability.DFA
public import Definitions.Def_LeanPool_Parikh_RegularRealization
public import Definitions.Def_LeanPool_Parikh_Statements
public import Definitions.Def_LeanPool_Parikh_Api
set_option autoImplicit true
@[expose] public section
public section
open Parikh

theorem Parikh.LinearComponent.isLinearSet {T : Type*} (c : LinearComponent T) :
    IsLinearSet c.denotation := by sorry
