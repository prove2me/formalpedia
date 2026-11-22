-- Prove2me | Theorems.Thm_Parikh_component_isLinearSet
-- name    : Parikh.component_isLinearSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:47:46.316427+00:00
-- url     : https://prove2.me/theorems/7fbbe923-f89f-45c4-85a9-b3883d028c05
-- title:
--   Parikh: component is Linear Set
-- statement:
--   Bridge indexed coefficient sums to Mathlib's finitely generated additive closure.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Counting.lean#L94-L97
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Counting.lean#L94-L97

module
public import Mathlib.Computability.Language
public import Mathlib.ModelTheory.Arithmetic.Presburger.Semilinear.Defs
public import Mathlib.Algebra.Group.Submonoid.Finsupp
public import Definitions.Def_LeanPool_Parikh_Counting
set_option autoImplicit true
@[expose] public section
public section
open scoped Pointwise
open Parikh

theorem Parikh.component_isLinearSet {T : Type*} (c : Component T) :
    IsLinearSet c.denotation := by sorry
