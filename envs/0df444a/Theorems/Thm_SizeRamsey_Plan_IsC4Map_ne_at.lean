-- Prove2me | Theorems.Thm_SizeRamsey_Plan_IsC4Map_ne_at
-- name    : SizeRamsey.Plan.IsC4Map.ne_at
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:20:22.68331+00:00
-- url     : https://prove2.me/theorems/3aea7f45-317a-4468-a4b4-10402e916399
-- title:
--   Is C4 Map: ne at
-- statement:
--   The Is C4 Map construction uses the ne at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Reductions.lean#L78-L79
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Reductions.lean#L78-L79

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
omit [Fintype V]

theorem SizeRamsey.Plan.IsC4Map.ne_at {g : Fin 4 → V} (hg : IsC4Map G g) (k : Fin 4) {a b : Fin 4}
    (h : a ≠ b) : g (k + a) ≠ g (k + b) := by sorry
