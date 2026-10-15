-- Prove2me | Theorems.Thm_ThreeSum_LayerCounts_rightFiber_card
-- name    : ThreeSum.LayerCounts.rightFiber_card
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:48:47.512431+00:00
-- url     : https://prove2.me/theorems/32ed58e3-ef24-49aa-96bc-67ee6b24feb6
-- title:
--   Every right vertex has the same disjointness degree
-- statement:
--   Let $L,h\in\mathbb N$ and let $V$ be an $h$-element subset of an $L$-element ground set. Let $E_{L,h}$ consist of ordered pairs of disjoint $h$-element subsets. Then
--
--   $$|\{(S,T)\in E_{L,h}:T=V\}|=\binom{L-h}{h}.$$
--
--   This exact right-degree formula is valid also when no disjoint partner exists. It supplies the symmetric fiber count used in the finite local-cover graph estimates.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LayerCounts.lean#L67-L81

import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Basic
import Theorems.Thm_ThreeSum_LayerCounts_leftFiber_card


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

theorem ThreeSum.LayerCounts.rightFiber_card : ∀ {L h : Nat} (V : Finset.{0} (Fin L)) (hV : @Eq.{1} Nat (@Finset.card.{0} (Fin L) V) h),
  @Eq.{1} Nat
    (@Finset.card.{0} (Prod.{0, 0} (Finset.{0} (Fin L)) (Finset.{0} (Fin L)))
      ({p ∈ ThreeSum.LayerCounts.edgeSet L h |
        @Eq.{1} (Finset.{0} (Fin L)) (@Prod.snd.{0, 0} (Finset.{0} (Fin L)) (Finset.{0} (Fin L)) p) V}))
    ((@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) L h).choose h) := by
  sorry
