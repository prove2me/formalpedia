-- Prove2me | Theorems.Thm_SizeRamsey_Plan_mixed_reconstruction
-- name    : SizeRamsey.Plan.mixed_reconstruction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:28:34.846278+00:00
-- url     : https://prove2.me/theorems/2e488bd1-1212-5f8b-be6f-d1737f3446c1
-- title:
--   Plan: mixed reconstruction
-- statement:
--   The Plan construction uses the mixed reconstruction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Equality/Mixed.lean#L368-L380
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Equality/Mixed.lean#L368-L380

module
public import Definitions.Def_SizeRamsey_Equality_Common
public import Definitions.Def_SizeRamsey_Equality_Mixed
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
universe u
attribute [local instance] Classical.propDecidable

theorem SizeRamsey.Plan.mixed_reconstruction
    {V : Type u} (G : SimpleGraph V)
    (f : Fin 6 ≃ V)
    (hadj : ∀ i j,
      G.Adj (f i) (f j) ↔ k33MinusEdge.Adj i j) :
    Nonempty (G ≃g k33MinusEdge) := by sorry
