-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_theta_eq
-- name    : PretorsionImageClosed.Statement.theta_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:12:31.650205+00:00
-- url     : https://prove2.me/theorems/976cb629-4638-406b-a533-5b99361aca15
-- title:
--   Statement: theta eq
-- statement:
--   Equation (8.5): `theta R = x^{|R| + 1} + q x² Δ_q(x^{|R|})`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Gandhi/ColumnSum.lean#L234-L244
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Gandhi/ColumnSum.lean#L234-L244

module
public import Definitions.Def_PretorsionImageClosed_Gandhi_Delta
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Definitions.Def_PretorsionImageClosed_Gandhi_ColumnSum
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open Polynomial Finset
variable {ι : Type*} [LinearOrder ι]

theorem PretorsionImageClosed.Statement.theta_eq (R : Finset ι) : theta R = X ^ (R.card + 1) + C q * X ^ 2 * deltaXPow R.card := by sorry
