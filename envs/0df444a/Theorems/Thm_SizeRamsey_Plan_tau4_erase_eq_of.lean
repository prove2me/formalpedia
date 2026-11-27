-- Prove2me | Theorems.Thm_SizeRamsey_Plan_tau4_erase_eq_of
-- name    : SizeRamsey.Plan.tau4_erase_eq_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:18:40.71448+00:00
-- url     : https://prove2.me/theorems/50e519a8-9197-4557-8bba-95d6c1200cb4
-- title:
--   Plan: tau4 erase eq of
-- statement:
--   `τ₄(erase G D) = τ₄(H)` when the squares of `H` avoid `D` and `H` agrees with `G` off `D`.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean#L110-L123
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean#L110-L123

module
public import Definitions.Def_SizeRamsey_Basic
public import Definitions.Def_SizeRamsey_Deletion
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable
variable {V : Type*} {W : Type*}

theorem SizeRamsey.Plan.tau4_erase_eq_of [Fintype V] (G H : SimpleGraph V) (D : Finset V)
    (havoid : ∀ f, IsC4Map H f → ∀ i, f i ∉ D)
    (hadj : ∀ a b, a ∉ D → b ∉ D → (H.Adj a b ↔ G.Adj a b)) :
    tau4 (erase G D) = tau4 H := by sorry
