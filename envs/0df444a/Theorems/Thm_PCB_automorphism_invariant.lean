-- Prove2me | Theorems.Thm_PCB_automorphism_invariant
-- name    : PCB.automorphism_invariant
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-22T20:15:57.977989+00:00
-- url     : https://prove2.me/theorems/7aefa415-2199-4f13-a3d2-6c3b03116381
-- title:
--   The lexicographic cone is invariant under decomposition-preserving automorphisms (Proposition 9)
-- statement:
--   The lexicographic cone is invariant under the automorphisms that preserve the almost-direct product decomposition. An automorphism mapping each free factor onto itself, whose restriction and inverse restriction preserve the Magnus-type cones, carries the lexicographic cone onto itself: it moves no components across factors and preserves the sign of the highest nontrivial one. This is Proposition 9 of the paper, which exhibits the rigidity of the lexicographic ordering.
-- source:
--   O. Ocampo, J. R. T. Theodoro de Lima, Positive cones and bi-orderings on almost-direct products of free groups, arXiv:2209.04706 (2022), Section 2 (Proposition 9).

import Mathlib
import Definitions.Def_PCB_alg
import Definitions.Def_PCB_tor

namespace PCB

/-!  Milestone 7 (Proposition 9): the lexicographic cone is invariant
under the automorphisms preserving the almost-direct product decomposition.
An automorphism mapping each free factor onto itself with cone-preserving
restriction - and whose inverse does the same - carries the lexicographic
cone onto itself, so it preserves the lexicographic bi-ordering. -/
theorem automorphism_invariant {k : ℕ} {G : Type*} [Group G] {F : Fin k → Type*} [∀ j, Group (F j)]
    (W : AlmostDirectProductWorld k G F) (φ : G ≃* G)
    (h : ∀ (j : Fin k) (f : F j), f ∈ W.cone j → ∃ f' ∈ W.cone j,
      ∀ i : Fin k, W.nf (φ (embedFactor W j f)) i = if h2 : i = j then h2 ▸ f' else 1)
    (hInv : ∀ (j : Fin k) (f : F j), f ∈ W.cone j → ∃ f' ∈ W.cone j,
      ∀ i : Fin k, W.nf (φ.symm (embedFactor W j f)) i = if h2 : i = j then h2 ▸ f' else 1) :
    (∀ g, g ∈ lexCone W → φ g ∈ lexCone W) ∧
    (∀ g, g ∈ lexCone W → φ.symm g ∈ lexCone W) := by sorry

end PCB
