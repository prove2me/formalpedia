-- Prove2me | Theorems.Thm_SizeRamsey_Plan_IsC4Map_adj_at
-- name    : SizeRamsey.Plan.IsC4Map.adj_at
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:20:25.975115+00:00
-- url     : https://prove2.me/theorems/366024d7-edbf-4171-94bd-8217a547b5cd
-- title:
--   Is C4 Map: adj at
-- statement:
--   The Is C4 Map construction uses the adj at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Reductions.lean#L68-L75
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Reductions.lean#L68-L75

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

theorem SizeRamsey.Plan.IsC4Map.adj_at {g : Fin 4 → V} (hg : IsC4Map G g) (k : Fin 4) :
    G.Adj (g k) (g (k + 1)) ∧ G.Adj (g (k + 1)) (g (k + 2)) ∧
      G.Adj (g (k + 2)) (g (k + 3)) ∧ G.Adj (g (k + 3)) (g k) := by sorry
