-- Prove2me | Theorems.Thm_SizeRamsey_Plan_hasC4_map
-- name    : SizeRamsey.Plan.hasC4_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:25:20.464379+00:00
-- url     : https://prove2.me/theorems/43a7c892-502a-4fda-9f8f-5cfcf8d22e31
-- title:
--   Plan: has C4 map
-- statement:
--   The Plan construction uses the has C4 map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Upper.lean#L113-L121
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Upper.lean#L113-L121

module
public import Definitions.Def_SizeRamsey_AInterface
public import Definitions.Def_SizeRamsey_Upper
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan

theorem SizeRamsey.Plan.hasC4_map {V W : Type*}
    {G : SimpleGraph V} {H : SimpleGraph W}
    (f : V → W) (hf : Function.Injective f)
    (hadj : ∀ ⦃a b⦄,
      G.Adj a b → H.Adj (f a) (f b)) :
    HasC4 G → HasC4 H := by sorry
