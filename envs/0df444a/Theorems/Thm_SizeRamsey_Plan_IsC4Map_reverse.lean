-- Prove2me | Theorems.Thm_SizeRamsey_Plan_IsC4Map_reverse
-- name    : SizeRamsey.Plan.IsC4Map.reverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:18:43.271976+00:00
-- url     : https://prove2.me/theorems/3c267b89-48be-40cf-ac53-60b612f174fb
-- title:
--   Is C4 Map: reverse
-- statement:
--   The Is C4 Map construction uses the reverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean#L47-L53
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean#L47-L53

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

theorem SizeRamsey.Plan.IsC4Map.reverse {G : SimpleGraph V} {f : Fin 4 → V} (hf : IsC4Map G f) (k : Fin 4) :
    IsC4Map G (fun i => f (k - i)) := by sorry
