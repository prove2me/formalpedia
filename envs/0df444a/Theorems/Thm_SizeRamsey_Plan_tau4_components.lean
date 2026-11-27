-- Prove2me | Theorems.Thm_SizeRamsey_Plan_tau4_components
-- name    : SizeRamsey.Plan.tau4_components
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:21:15.442196+00:00
-- url     : https://prove2.me/theorems/cb268cef-1357-4704-8625-62a36b48705e
-- title:
--   Plan: tau4 components
-- statement:
--   The Plan construction uses the tau4 components property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Components.lean#L27-L63
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Components.lean#L27-L63

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

theorem SizeRamsey.Plan.tau4_components :
    tau4 G =
      ∑ C : G.ConnectedComponent, tau4 (compGraph G C) := by sorry
