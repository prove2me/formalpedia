-- Prove2me | Theorems.Thm_PebblingLean_Pebbling_solvable_product_of_fiber_demands
-- name    : PebblingLean.Pebbling.solvable_product_of_fiber_demands
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:46:42.478798+00:00
-- url     : https://prove2.me/theorems/8f20e913-677e-46dd-8f00-81145721d6cd
-- title:
--   Pebbling: solvable product of fiber demands
-- statement:
--   Deterministic product step.  If `E` solves `H`, and each `z`-fiber has
--   enough demand-solvability in `G` to prepare `E z` pebbles at any chosen
--   first-coordinate target, then the assembled product distribution solves
--   `G □ H`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Product.lean#L312-L324
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Product.lean#L312-L324

module
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Definitions.Def_LeanPool_PebblingLean_Product
set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u v
open PebblingLean.Pebbling
variable {V : Type u} {W : Type v}

theorem PebblingLean.Pebbling.solvable_product_of_fiber_demands [Finite W] [DecidableEq V] [DecidableEq W]
    {G : Graph V} {H : Graph W} {E : Pebbling W} {F : W → Pebbling V}
    (hE : Solvable H E)
    (hF : ∀ z : W, SolvableAtLeast G (F z) (E z)) :
    Solvable (Graph.cartesianProduct G H) (fibersDistribution F) := by sorry
