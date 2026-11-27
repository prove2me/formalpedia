-- Prove2me | Theorems.Thm_SizeRamsey_Plan_equality_cubic_impossible
-- name    : SizeRamsey.Plan.equality_cubic_impossible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:24:53.565048+00:00
-- url     : https://prove2.me/theorems/d13f969e-ed02-4299-b1e7-def09068085e
-- title:
--   Plan: equality cubic impossible
-- statement:
--   The Plan construction uses the equality cubic impossible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Equality/Cubic.lean#L178-L269
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Equality/Cubic.lean#L178-L269

module
public import Definitions.Def_SizeRamsey_Equality_Common
public import Definitions.Def_SizeRamsey_Equality_Cubic
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
universe u
attribute [local instance] Classical.propDecidable

theorem SizeRamsey.Plan.equality_cubic_impossible
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hc : G.Connected)
    (hp : 0 < edgeCount G)
    (hm : edgeCount G ≤ 16)
    (ht : Tight G)
    (ih : SmallerClassified G)
    (h3 : ∀ v, G.degree v = 3) :
    False := by sorry
