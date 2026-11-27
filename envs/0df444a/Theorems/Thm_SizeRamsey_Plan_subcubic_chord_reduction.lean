-- Prove2me | Theorems.Thm_SizeRamsey_Plan_subcubic_chord_reduction
-- name    : SizeRamsey.Plan.subcubic_chord_reduction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:20:57.161363+00:00
-- url     : https://prove2.me/theorems/cdfc601b-5e42-5ac4-b1de-189659ab1731
-- title:
--   Plan: subcubic chord reduction
-- statement:
--   The Plan construction uses the subcubic chord reduction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Reductions.lean#L227-L313
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Reductions.lean#L227-L313

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

theorem SizeRamsey.Plan.subcubic_chord_reduction
    (hdeg : ∀ v, G.degree v ≤ 3)
    (f : Fin 4 → V) (hf : IsC4Map G f)
    (hac : G.Adj (f 0) (f 2)) :
    tau4 G ≤ tau4 (erase G {f 0,f 1,f 2}) + 1 ∧
    edgeCount (erase G {f 0,f 1,f 2}) +
      G.degree (f 1) + 3 = edgeCount G ∧
    2 ≤ G.degree (f 1) := by sorry
