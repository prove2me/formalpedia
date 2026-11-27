-- Prove2me | Theorems.Thm_SizeRamsey_Plan_star_or_empty
-- name    : SizeRamsey.Plan.star_or_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:24:59.569158+00:00
-- url     : https://prove2.me/theorems/3bd8899c-f16b-54de-90b1-1e76690db4fe
-- title:
--   Plan: star or empty
-- statement:
--   The Plan construction uses the star or empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Upper.lean#L41-L74
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Upper.lean#L41-L74

module
public import Definitions.Def_SizeRamsey_AInterface
public import Definitions.Def_SizeRamsey_Upper
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan

theorem SizeRamsey.Plan.star_or_empty {V : Type*} (G : SimpleGraph V)
    (htri : ∀ a b c,
      G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hmatch : ¬ HasMatching2 G) :
    G = ⊥ ∨
      ∃ v, ∀ a b, G.Adj a b → a = v ∨ b = v := by sorry
