-- Prove2me | Theorems.Thm_SizeRamsey_Plan_sum_fin_four
-- name    : SizeRamsey.Plan.sum_fin_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:24:14.566092+00:00
-- url     : https://prove2.me/theorems/69bbc094-b1de-4523-a790-3e261d5b17ac
-- title:
--   Plan: sum fin four
-- statement:
--   The Plan construction uses the sum fin four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Reductions.lean#L64-L65
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Reductions.lean#L64-L65

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

theorem SizeRamsey.Plan.sum_fin_four (c : Fin 4 → ℕ) : ∑ i, c i = c 0 + c 1 + c 2 + c 3 := by sorry
