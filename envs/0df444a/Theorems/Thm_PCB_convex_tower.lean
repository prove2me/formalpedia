-- Prove2me | Theorems.Thm_PCB_convex_tower
-- name    : PCB.convex_tower
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-22T20:10:16.211007+00:00
-- url     : https://prove2.me/theorems/d4e98c4c-ee38-42df-b535-7dac3025bdfd
-- title:
--   The canonical filtration subgroups are convex (Proposition 8)
-- statement:
--   The canonical filtration subgroups are convex for the lexicographic bi-ordering. An element outside a filtration subgroup has a nontrivial normal-form component above the given index, so it lies either above every element of the subgroup or below every element of the subgroup, and no element outside the subgroup can lie strictly between two of its elements. This is Proposition 8 of the paper.
-- source:
--   O. Ocampo, J. R. T. Theodoro de Lima, Positive cones and bi-orderings on almost-direct products of free groups, arXiv:2209.04706 (2022), Section 2 (Proposition 8).

import Mathlib
import Definitions.Def_PCB_alg
import Definitions.Def_PCB_tor

namespace PCB

/-!  Milestone 6 (Proposition 8): the canonical subgroups of the
filtration are convex with respect to the lexicographic bi-ordering. An
element outside the subgroup G_j has a nontrivial component above j, so
it lies either above every element of G_j or below every element of G_j
in the order, and no element outside G_j can lie strictly between two of
its elements. -/
theorem convex_tower {k : ℕ} {G : Type*} [Group G] {F : Fin k → Type*} [∀ j, Group (F j)]
    (W : AlmostDirectProductWorld k G F) :
    ∀ j : Fin k, ConvexSubgroup (lexCone W) (W.tower j) := by sorry

end PCB
