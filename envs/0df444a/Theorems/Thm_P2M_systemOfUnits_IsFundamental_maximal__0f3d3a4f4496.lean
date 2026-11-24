-- Prove2me | Theorems.Thm_P2M_systemOfUnits_IsFundamental_maximal__0f3d3a4f4496
-- name    : P2M_systemOfUnits_IsFundamental_maximal__0f3d3a4f4496
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:37:28.049732+00:00
-- url     : https://prove2.me/theorems/277cf9b3-a9f3-4772-a80b-8ac53a9bfab8
-- title:
--   P2 M system Of Units Is Fundamental maximal  0f3d3a4f4496: P2 M system Of Units Is Fundamental maximal  0f3d3a4f4496
-- statement:
--   The P2 M system Of Units Is Fundamental maximal  0f3d3a4f4496 construction uses the P2 M system Of Units Is Fundamental maximal  0f3d3a4f4496 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Hilbert92.lean#L52-L57
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Hilbert92.lean#L52-L57

module
public import Definitions.Def_FltRegular_NumberTheory_SystemOfUnits
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.RingTheory.Henselian
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
public import Mathlib.LinearAlgebra.Dimension.Torsion.Basic
public import Definitions.Def_FltRegular_NumberTheory_Hilbert92
set_option autoImplicit false
@[expose] public section
public section
open scoped NumberField nonZeroDivisors
open FiniteDimensional NumberField
variable {s r : ℕ} (p : ℕ) {K : Type*} [Field K]
variable {k : Type*} [Field k] (hp : Nat.Prime p)
open Module Finset
open CyclotomicIntegers (zeta)
variable (G : Type*) [AddCommGroup G]
local notation3 "A" => CyclotomicIntegers p

theorem P2M_systemOfUnits_IsFundamental_maximal__0f3d3a4f4496 [Module A G] (S : systemOfUnits p G r)
    (hs : S.IsFundamental) (a : systemOfUnits p G r) [a.IsMaximal] :
    (Submodule.span A (Set.range S.units)).toAddSubgroup.index ≤
      (Submodule.span A (Set.range a.units)).toAddSubgroup.index := by sorry

alias «systemOfUnits».«IsFundamental».«maximal'» := P2M_systemOfUnits_IsFundamental_maximal__0f3d3a4f4496
