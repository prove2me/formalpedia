-- Prove2me | Theorems.Thm_SizeRamsey_Plan_matching2_union
-- name    : SizeRamsey.Plan.matching2_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:25:17.236555+00:00
-- url     : https://prove2.me/theorems/0f66da75-8947-4362-98a7-5145704852c1
-- title:
--   Plan: matching2 union
-- statement:
--   The Plan construction uses the matching2 union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Upper.lean#L123-L141
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Upper.lean#L123-L141

module
public import Definitions.Def_SizeRamsey_AInterface
public import Definitions.Def_SizeRamsey_Upper
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan

theorem SizeRamsey.Plan.matching2_union {V W : Type*}
    {G H : SimpleGraph V} {F : SimpleGraph W}
    (i j : V → W)
    (hi : Function.Injective i)
    (hj : Function.Injective j)
    (hdis : ∀ a b, i a ≠ j b)
    (hG : ∀ ⦃a b⦄,
      G.Adj a b → F.Adj (i a) (i b))
    (hH : ∀ ⦃a b⦄,
      H.Adj a b → F.Adj (j a) (j b)) :
    HasMatching2 G → HasMatching2 H → HasMatching4 F := by sorry
