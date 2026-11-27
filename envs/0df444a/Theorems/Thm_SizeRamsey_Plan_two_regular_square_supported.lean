-- Prove2me | Theorems.Thm_SizeRamsey_Plan_two_regular_square_supported
-- name    : SizeRamsey.Plan.two_regular_square_supported
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:22:11.095028+00:00
-- url     : https://prove2.me/theorems/d3e103fb-5091-5993-a120-40b0eb4ce4dc
-- title:
--   Plan: two regular square supported
-- statement:
--   The Plan construction uses the two regular square supported property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Reductions.lean#L133-L175
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Reductions.lean#L133-L175

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

theorem SizeRamsey.Plan.two_regular_square_supported
    (hcon : G.Connected) (hsq : SquareSupported G)
    (hdeg : ∀ v, G.degree v = 2) :
    Nonempty (G ≃g SimpleGraph.cycleGraph 4) := by sorry
