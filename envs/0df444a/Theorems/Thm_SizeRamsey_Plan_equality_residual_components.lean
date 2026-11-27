-- Prove2me | Theorems.Thm_SizeRamsey_Plan_equality_residual_components
-- name    : SizeRamsey.Plan.equality_residual_components
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:24:28.876199+00:00
-- url     : https://prove2.me/theorems/33b1c1dc-d986-4356-beaa-3be254d22a23
-- title:
--   Plan: equality residual components
-- statement:
--   The Plan construction uses the equality residual components property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Tightness.lean#L55-L75
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Tightness.lean#L55-L75

module
public import Definitions.Def_SizeRamsey_Universal
public import Definitions.Def_SizeRamsey_Tightness
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

theorem SizeRamsey.Plan.equality_residual_components
    (D : Finset V) (c : ℕ)
    (ht : 4 * tau4 G = edgeCount G)
    (hlift : tau4 G ≤ tau4 (erase G D) + c)
    (hcount : edgeCount (erase G D) + 4 * c = edgeCount G) :
    tau4 G = tau4 (erase G D) + c ∧
    ∀ C : (erase G D).ConnectedComponent,
      4 * tau4 (compGraph (erase G D) C) =
        edgeCount (compGraph (erase G D) C) := by sorry
