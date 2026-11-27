-- Prove2me | Theorems.Thm_SizeRamsey_Plan_square_supported_degree_ge_two
-- name    : SizeRamsey.Plan.square_supported_degree_ge_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:20:54.360229+00:00
-- url     : https://prove2.me/theorems/808f49c6-1384-46ab-b88a-838c1b81470e
-- title:
--   Plan: square supported degree ge two
-- statement:
--   The Plan construction uses the square supported degree ge two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Reductions.lean#L81-L90
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Reductions.lean#L81-L90

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

theorem SizeRamsey.Plan.square_supported_degree_ge_two
    (hs : SquareSupported G) (v : V)
    (hv : 0 < G.degree v) :
    2 ≤ G.degree v := by sorry
