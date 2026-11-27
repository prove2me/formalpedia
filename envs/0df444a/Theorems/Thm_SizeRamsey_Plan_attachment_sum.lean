-- Prove2me | Theorems.Thm_SizeRamsey_Plan_attachment_sum
-- name    : SizeRamsey.Plan.attachment_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:21:59.604267+00:00
-- url     : https://prove2.me/theorems/374fbf69-ff6f-5082-8d63-96ff92b890c9
-- title:
--   Plan: attachment sum
-- statement:
--   The Plan construction uses the attachment sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Components.lean#L212-L254
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Components.lean#L212-L254

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

theorem SizeRamsey.Plan.attachment_sum (D : Finset V) :
    (∑ C : (erase G D).ConnectedComponent,
      (attachmentEdges G D C).card) +
      2 * edgeCount (G.induce (D : Set V)) =
        ∑ v ∈ D, G.degree v := by sorry
