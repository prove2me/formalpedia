-- Prove2me | Theorems.Thm_ThreeSum_LayerCounts_leftFiber_card
-- name    : ThreeSum.LayerCounts.leftFiber_card
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T06:42:16.798832+00:00
-- url     : https://prove2.me/theorems/3cb3f5bd-d760-40b5-b90b-39246826c053
-- title:
--   Exact degree of the disjoint-subset graph
-- statement:
--   Let $L,h\in\mathbb N$ and fix a subset $S\subseteq\{0,\ldots,L-1\}$ with $|S|=h$. In the graph whose edges are ordered pairs of disjoint $h$-element subsets, the number of edges with left endpoint $S$ is
--
--   $$
--   \bigl|\{(S,T):T\subseteq\{0,\ldots,L-1\},\ |T|=h,\ S\cap T=\varnothing\}\bigr|
--   =\binom{L-h}{h}.
--   $$
--
--   There is no additional requirement that $2h\le L$; when there is insufficient room for a disjoint partner, the binomial coefficient is zero.
--
--   This determines the exact vertex degree used in the local-cover graph counts and their numerical bounds.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LayerCounts.lean#L37-L65

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

theorem ThreeSum.LayerCounts.leftFiber_card : ∀ {L h : Nat} (S : Finset.{0} (Fin L)) (hS : @Eq.{1} Nat (@Finset.card.{0} (Fin L) S) h),
  @Eq.{1} Nat
    (@Finset.card.{0} (Prod.{0, 0} (Finset.{0} (Fin L)) (Finset.{0} (Fin L)))
      ({p ∈ ThreeSum.LayerCounts.edgeSet L h |
        @Eq.{1} (Finset.{0} (Fin L)) (@Prod.fst.{0, 0} (Finset.{0} (Fin L)) (Finset.{0} (Fin L)) p) S}))
    ((@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) L h).choose h) := by
  sorry
