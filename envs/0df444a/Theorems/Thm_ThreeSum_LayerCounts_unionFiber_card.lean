-- Prove2me | Theorems.Thm_ThreeSum_LayerCounts_unionFiber_card
-- name    : ThreeSum.LayerCounts.unionFiber_card
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T06:42:31.94424+00:00
-- url     : https://prove2.me/theorems/02677c92-3ba5-4b6c-8406-f1aefa3fd622
-- title:
--   Exact number of ordered disjoint-subset pairs with fixed union
-- statement:
--   Let $L,h\in\mathbb N$ and let $Q\subseteq\{0,\ldots,L-1\}$ have cardinality $2h$. The number of ordered pairs of disjoint $h$-element subsets whose union is $Q$ is
--
--   $$
--   \bigl|\{(S,T):|S|=|T|=h,\ S\cap T=\varnothing,\ S\cup T=Q\}\bigr|
--   =\binom{2h}{h}.
--   $$
--
--   The pairs are ordered, so exchanging the two subsets is not identified. The statement includes the empty case $h=0$.
--
--   This gives the exact number of graph representations of a single output subset, a quantity used in the local hash-cover counting estimates.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LayerCounts.lean#L83-L107

import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Basic


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

theorem ThreeSum.LayerCounts.unionFiber_card : ∀ {L h : Nat} (Q : Finset.{0} (Fin L))
  (hQ :
    @Eq.{1} Nat (@Finset.card.{0} (Fin L) Q)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h)),
  @Eq.{1} Nat
    (@Finset.card.{0} (Prod.{0, 0} (Finset.{0} (Fin L)) (Finset.{0} (Fin L)))
      ({p ∈ ThreeSum.LayerCounts.edgeSet L h |
        @Eq.{1} (Finset.{0} (Fin L))
          (@Union.union.{0} (Finset.{0} (Fin L)) (@Finset.instUnion.{0} (Fin L) (instDecidableEqFin L))
            (@Prod.fst.{0, 0} (Finset.{0} (Fin L)) (Finset.{0} (Fin L)) p)
            (@Prod.snd.{0, 0} (Finset.{0} (Fin L)) (Finset.{0} (Fin L)) p))
          Q}))
    ((@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h).choose
      h) := by
  sorry
