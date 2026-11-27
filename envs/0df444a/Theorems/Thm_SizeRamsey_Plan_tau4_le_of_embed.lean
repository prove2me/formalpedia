-- Prove2me | Theorems.Thm_SizeRamsey_Plan_tau4_le_of_embed
-- name    : SizeRamsey.Plan.tau4_le_of_embed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:18:49.311808+00:00
-- url     : https://prove2.me/theorems/54185e93-6fc1-494e-9f7e-a78d0feec05b
-- title:
--   Plan: tau4 le of embed
-- statement:
--   If every square of `G` is the `g`-image of a square of `H` (`g` injective),
--   `τ₄(G) ≤ τ₄(H)`.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean#L93-L102
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean#L93-L102

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

theorem SizeRamsey.Plan.tau4_le_of_embed [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}
    (g : W → V)
    (hsq : ∀ f, IsC4Map G f → ∃ f', IsC4Map H f' ∧ g ∘ f' = f) : tau4 G ≤ tau4 H := by sorry
