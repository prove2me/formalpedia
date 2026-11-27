-- Prove2me | Theorems.Thm_SizeRamsey_Plan_isC4Map_iff_cyclic
-- name    : SizeRamsey.Plan.isC4Map_iff_cyclic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:18:18.838822+00:00
-- url     : https://prove2.me/theorems/2603f8e9-e641-55f8-a95d-0b27da54c6e4
-- title:
--   Plan: is C4 Map iff cyclic
-- statement:
--   The Plan construction uses the is C4 Map iff cyclic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean#L30-L38
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean#L30-L38

module
public import Definitions.Def_SizeRamsey_Basic
public import Definitions.Def_SizeRamsey_Deletion
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable
variable {V : Type*} {W : Type*}

theorem SizeRamsey.Plan.isC4Map_iff_cyclic {G : SimpleGraph V} {f : Fin 4 → V} :
    IsC4Map G f ↔ Function.Injective f ∧ ∀ i, G.Adj (f i) (f (i + 1)) := by sorry
