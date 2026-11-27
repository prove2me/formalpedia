-- Prove2me | Theorems.Thm_SizeRamsey_Plan_classified_three_degree_two
-- name    : SizeRamsey.Plan.classified_three_degree_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:24:13.630795+00:00
-- url     : https://prove2.me/theorems/5310d86b-f251-50d8-a052-829eef163f68
-- title:
--   Plan: classified three degree two
-- statement:
--   The Plan construction uses the classified three degree two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/SmallGraphs.lean#L181-L210
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/SmallGraphs.lean#L181-L210

module
public import Definitions.Def_SizeRamsey_FiniteChecks
public import Definitions.Def_SizeRamsey_SmallGraphs
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable

theorem SizeRamsey.Plan.classified_three_degree_two
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (h : Classified G) (a b c : V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : G.degree a = 2)
    (hb : G.degree b = 2)
    (hc : G.degree c = 2) :
    Nonempty (G ≃g SimpleGraph.cycleGraph 4) := by sorry
