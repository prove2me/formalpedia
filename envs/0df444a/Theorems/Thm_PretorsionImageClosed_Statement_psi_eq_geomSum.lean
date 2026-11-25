-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_psi_eq_geomSum
-- name    : PretorsionImageClosed.Statement.psi_eq_geomSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:11:57.298049+00:00
-- url     : https://prove2.me/theorems/4628de37-0d99-469b-bc75-619b440f0785
-- title:
--   Statement: psi eq geom Sum
-- statement:
--   Lemma 7.3: `psi R = Δ_q(x^{|R| + 1})`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Gandhi/ColumnSum.lean#L147-L152
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Gandhi/ColumnSum.lean#L147-L152

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

theorem PretorsionImageClosed.Statement.psi_eq_geomSum (R : Finset ι) : psi R = geomSum R.card := by sorry
