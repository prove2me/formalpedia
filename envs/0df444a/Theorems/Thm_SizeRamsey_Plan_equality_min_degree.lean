-- Prove2me | Theorems.Thm_SizeRamsey_Plan_equality_min_degree
-- name    : SizeRamsey.Plan.equality_min_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:21:54.442712+00:00
-- url     : https://prove2.me/theorems/edc14b2d-200e-5ae1-a5d1-8efe8534100a
-- title:
--   Plan: equality min degree
-- statement:
--   The Plan construction uses the equality min degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Tightness.lean#L47-L53
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Tightness.lean#L47-L53

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

theorem SizeRamsey.Plan.equality_min_degree
    (hcon : G.Connected) (hm : 0 < edgeCount G)
    (ht : 4 * tau4 G = edgeCount G) :
    ∀ v, 2 ≤ G.degree v := by sorry
