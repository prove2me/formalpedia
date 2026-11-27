-- Prove2me | Theorems.Thm_SizeRamsey_Plan_equality_square_supported
-- name    : SizeRamsey.Plan.equality_square_supported
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:21:40.972792+00:00
-- url     : https://prove2.me/theorems/5f115152-fe9e-44dc-a34a-eb37f703f8c2
-- title:
--   Plan: equality square supported
-- statement:
--   The Plan construction uses the equality square supported property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Tightness.lean#L27-L34
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Tightness.lean#L27-L34

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

theorem SizeRamsey.Plan.equality_square_supported
    (ht : 4 * tau4 G = edgeCount G) :
    SquareSupported G := by sorry
