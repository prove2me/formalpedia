-- Prove2me | Theorems.Thm_Positive_extension_unique
-- name    : Positive.extension_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:17:39.514827+00:00
-- url     : https://prove2.me/theorems/ac327295-e781-4012-9bc7-02af928daf34
-- title:
--   Positive: extension unique
-- statement:
--   The extension is the unique linear operator extending τ on nonnegative elements.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Operators/Positive.lean#L292-L298
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Operators/Positive.lean#L292-L298

module
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Mathlib.Algebra.Order.Module.Basic
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.Module.Equiv
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Operators_Positive
set_option autoImplicit true
@[expose] public section
public section
variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] [Lattice X] [Lattice Y]
  [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y] [VectorLattice X] [VectorLattice Y]
open Positive
variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] [Lattice X] [Lattice Y]
  [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y] [VectorLattice X] [VectorLattice Y]
  [IsVLArchimedean Y] {τ : X → Y}
variable
  (hτ_nn : ∀ x, 0 ≤ x → 0 ≤ τ x)
  (hτ_add : ∀ x y, 0 ≤ x → 0 ≤ y → τ (x + y) = τ x + τ y)

theorem Positive.extension_unique {f : X →ₗ[ℝ] Y}
    (hext : ∀ x, 0 ≤ x → f x = τ x) :
    f = extension hτ_nn hτ_add := by sorry
