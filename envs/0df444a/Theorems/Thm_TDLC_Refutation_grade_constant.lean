-- Prove2me | Theorems.Thm_TDLC_Refutation_grade_constant
-- name    : TDLC.Refutation.grade_constant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:24:44.679108+00:00
-- url     : https://prove2.me/theorems/8911f7a5-7051-4acb-a146-35a0bd73d1bc
-- title:
--   Refutation: grade constant
-- statement:
--   The Refutation construction uses the grade constant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Refutation.lean#L58-L69
-- source:
--   https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Refutation.lean#L58-L69

import Definitions.Def_TDLC_Solution
import Definitions.Def_TDLC_Refutation
set_option autoImplicit true
open TDLC TDLC.Refutation
universe u v
variable {G : Type v} (g : GroupData G) (mark : Marker.{u})

theorem TDLC.Refutation.grade_constant {A : Type u} {x y : A} (s : Step x y)
    (val : A → G) (c : G) (hc : ∀ x, val x = c) : grade g mark s val = g.one := by sorry
