-- Prove2me | Theorems.Thm_SizeRamsey_Plan_two_squares_matching_transversal
-- name    : SizeRamsey.Plan.two_squares_matching_transversal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:24:49.254227+00:00
-- url     : https://prove2.me/theorems/5e3ce647-adfd-43e4-ad09-0771bc6d3230
-- title:
--   Plan: two squares matching transversal
-- statement:
--   The Plan construction uses the two squares matching transversal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Equality/Cubic.lean#L21-L93
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Equality/Cubic.lean#L21-L93

module
public import Definitions.Def_SizeRamsey_Equality_Common
public import Definitions.Def_SizeRamsey_Equality_Cubic
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
universe u
attribute [local instance] Classical.propDecidable

theorem SizeRamsey.Plan.two_squares_matching_transversal
    {V : Type u} (G : SimpleGraph V)
    (l r : Fin 4 → V) (μ : Fin 4 ≃ Fin 4)
    (hl : Function.Injective l)
    (hr : Function.Injective r)
    (hdisj : ∀ i j, l i ≠ r j)
    (hcover : ∀ v,
      (∃ i, l i = v) ∨ ∃ j, r j = v)
    (hleft : ∀ i j,
      G.Adj (l i) (l j) ↔
        (SimpleGraph.cycleGraph 4).Adj i j)
    (hright : ∀ i j,
      G.Adj (r i) (r j) ↔
        (SimpleGraph.cycleGraph 4).Adj i j)
    (hcross : ∀ i j,
      G.Adj (l i) (r j) ↔ μ i = j) :
    c4Transversal G {l 0, r (μ 2)} := by sorry
