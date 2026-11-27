-- Prove2me | Theorems.Thm_SizeRamsey_Plan_component_attachment_card_ge_two
-- name    : SizeRamsey.Plan.component_attachment_card_ge_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:21:56.905126+00:00
-- url     : https://prove2.me/theorems/0c838644-6df8-5ca5-b214-46ac7b0dd9ad
-- title:
--   Plan: component attachment card ge two
-- statement:
--   The Plan construction uses the component attachment card ge two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Components.lean#L165-L210
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Components.lean#L165-L210

module
public import Definitions.Def_SizeRamsey_Deletion
public import Definitions.Def_SizeRamsey_Components
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

theorem SizeRamsey.Plan.component_attachment_card_ge_two
    (hcon : G.Connected) (hsq : SquareSupported G)
    (D : Finset V) (hD : D.Nonempty)
    (hproper : D ≠ Finset.univ)
    (C : (erase G D).ConnectedComponent) :
    2 ≤ (attachmentEdges G D C).card := by sorry
