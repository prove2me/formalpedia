-- Prove2me | Theorems.Thm_Parikh_Component_denotation_eq_vadd_closure
-- name    : Parikh.Component.denotation_eq_vadd_closure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:47:44.401687+00:00
-- url     : https://prove2.me/theorems/0fbce8e8-7d35-4375-8946-70114d5e8e0f
-- title:
--   Component: denotation eq vadd closure
-- statement:
--   Indexed period sums are exactly the additive closure of the period values.
--   This reuses Mathlib's finite-range closure theorem, including repeated and zero periods.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Counting.lean#L81-L91
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Counting.lean#L81-L91

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

theorem Parikh.Component.denotation_eq_vadd_closure {T : Type*} (c : Component T) :
    c.denotation = c.base +ᵥ
      (AddSubmonoid.closure (Set.range c.periods.get) : Set (Vector T)) := by sorry
