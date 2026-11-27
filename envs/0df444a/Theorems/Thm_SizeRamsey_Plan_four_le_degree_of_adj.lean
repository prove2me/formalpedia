-- Prove2me | Theorems.Thm_SizeRamsey_Plan_four_le_degree_of_adj
-- name    : SizeRamsey.Plan.four_le_degree_of_adj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:20:48.195593+00:00
-- url     : https://prove2.me/theorems/49fe256b-f0d4-5289-ad52-952d91468e3d
-- title:
--   Plan: four le degree of adj
-- statement:
--   The Plan construction uses the four le degree of adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Reductions.lean#L46-L52
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Reductions.lean#L46-L52

module
public import Definitions.Def_SizeRamsey_Components
public import Definitions.Def_SizeRamsey_SmallGraphs
public import Definitions.Def_SizeRamsey_Reductions
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

theorem SizeRamsey.Plan.four_le_degree_of_adj {x a b c d : V} (ha : G.Adj x a) (hb : G.Adj x b)
    (hc : G.Adj x c) (hd : G.Adj x d) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    4 ≤ G.degree x := by sorry
