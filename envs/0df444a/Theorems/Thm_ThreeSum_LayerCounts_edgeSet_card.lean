-- Prove2me | Theorems.Thm_ThreeSum_LayerCounts_edgeSet_card
-- name    : ThreeSum.LayerCounts.edgeSet_card
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:48:41.872103+00:00
-- url     : https://prove2.me/theorems/c39feef8-c600-4e60-9c0f-9d8f64bd26bb
-- title:
--   Counting ordered disjoint pairs in a uniform subset layer
-- statement:
--   Let $L,h\in\mathbb N$, and let $E_{L,h}$ be the set of ordered pairs $(S,T)$ of disjoint $h$-element subsets of an $L$-element ground set. Then
--
--   $$|E_{L,h}|=\binom{L}{2h}\binom{2h}{h}.$$
--
--   The formula includes empty layers when $2h>L$. It gives the exact edge count for the local disjointness graph and separates the number of union outputs from their ordered representations.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LayerCounts.lean#L114-L128

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

theorem ThreeSum.LayerCounts.edgeSet_card : ∀ (L h : Nat),
  @Eq.{1} Nat
    (@Finset.card.{0} (Prod.{0, 0} (Finset.{0} (Fin L)) (Finset.{0} (Fin L))) (ThreeSum.LayerCounts.edgeSet L h))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (L.choose
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h))
      ((@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h).choose
        h)) := by
  sorry
