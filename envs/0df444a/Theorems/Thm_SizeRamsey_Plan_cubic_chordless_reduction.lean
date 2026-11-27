-- Prove2me | Theorems.Thm_SizeRamsey_Plan_cubic_chordless_reduction
-- name    : SizeRamsey.Plan.cubic_chordless_reduction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:22:10.587688+00:00
-- url     : https://prove2.me/theorems/6f15e369-2340-5260-afc8-4bc4e87b7245
-- title:
--   Plan: cubic chordless reduction
-- statement:
--   The Plan construction uses the cubic chordless reduction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Reductions.lean#L177-L225
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Reductions.lean#L177-L225

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

theorem SizeRamsey.Plan.cubic_chordless_reduction
    (f : Fin 4 → V)
    (hdeg : ∀ i, G.degree (f i) = 3)
    (hf : IsC4Map G f)
    (hac : ¬ G.Adj (f 0) (f 2))
    (hbd : ¬ G.Adj (f 1) (f 3)) :
    tau4 G ≤ tau4 (erase G (Finset.univ.image f)) + 2 ∧
    edgeCount (erase G (Finset.univ.image f)) + 8 =
      edgeCount G := by sorry
