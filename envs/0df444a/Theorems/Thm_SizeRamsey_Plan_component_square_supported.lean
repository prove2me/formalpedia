-- Prove2me | Theorems.Thm_SizeRamsey_Plan_component_square_supported
-- name    : SizeRamsey.Plan.component_square_supported
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:21:29.052556+00:00
-- url     : https://prove2.me/theorems/98b1efcb-fdac-4287-9ce5-aaf6665ead86
-- title:
--   Plan: component square supported
-- statement:
--   The Plan construction uses the component square supported property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Components.lean#L110-L123
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Components.lean#L110-L123

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

theorem SizeRamsey.Plan.component_square_supported
    (hsq : SquareSupported G) (C : G.ConnectedComponent) :
    SquareSupported (compGraph G C) := by sorry
