-- Prove2me | Theorems.Thm_P2M_abs_smul__56c684b926d9
-- name    : P2M_abs_smul__56c684b926d9
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:10:43.480529+00:00
-- url     : https://prove2.me/theorems/da9fcee0-e1bc-4f9d-8d00-27ec8cf437e1
-- title:
--   P2 M abs smul  56c684b926d9: P2 M abs smul  56c684b926d9
-- statement:
--   `|a • x| = |a| • |x|` in a vector lattice.
--   Extends the Mathlib result of the same name from total orders to lattice orders.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Basic.lean#L367-L377
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Basic.lean#L367-L377

module
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Basic
set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
variable (x y : X)

theorem P2M_abs_smul__56c684b926d9 (a : ℝ) : |a • x| = |a| • |x| := by sorry

alias «abs_smul'» := P2M_abs_smul__56c684b926d9
