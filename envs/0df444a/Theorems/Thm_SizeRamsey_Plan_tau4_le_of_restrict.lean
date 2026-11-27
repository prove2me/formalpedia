-- Prove2me | Theorems.Thm_SizeRamsey_Plan_tau4_le_of_restrict
-- name    : SizeRamsey.Plan.tau4_le_of_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:18:27.978875+00:00
-- url     : https://prove2.me/theorems/2c1ff75f-94e0-51cf-b7fd-31570e5b21db
-- title:
--   Plan: tau4 le of restrict
-- statement:
--   If `g` sends squares of `G` to squares of `H` injectively, `τ₄(G) ≤ τ₄(H)`.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean#L80-L89
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean#L80-L89

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

theorem SizeRamsey.Plan.tau4_le_of_restrict [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}
    (g : V → W) (hg : Function.Injective g)
    (hsq : ∀ f, IsC4Map G f → IsC4Map H (g ∘ f)) : tau4 G ≤ tau4 H := by sorry
