-- Prove2me | Theorems.Thm_PCB_projection_compatible
-- name    : PCB.projection_compatible
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-22T20:09:51.597452+00:00
-- url     : https://prove2.me/theorems/d8a9befc-34b8-4915-ba1d-9d16ee52c346
-- title:
--   The lexicographic ordering extends the Magnus-type orderings of the factors (Proposition 6)
-- statement:
--   The lexicographic bi-ordering extends the Magnus-type orderings of the free factors. The embedding of a positive element of a factor into the product has that element as its single nontrivial normal-form component, so it lies in the lexicographic cone, and the restriction of the lexicographic ordering to each factor recovers the given Magnus-type ordering. This is Proposition 6 of the paper.
-- source:
--   O. Ocampo, J. R. T. Theodoro de Lima, Positive cones and bi-orderings on almost-direct products of free groups, arXiv:2209.04706 (2022), Section 2 (Proposition 6).

import Mathlib
import Definitions.Def_PCB_alg
import Definitions.Def_PCB_tor

namespace PCB

/-!  Milestone 5 (Proposition 6): the lexicographic bi-ordering extends
the Magnus-type orderings of the free factors. The embedding of a positive
element of a factor into the product lies in the lexicographic cone, and
its j-th component is the element itself, so the restriction of the
ordering to each factor recovers the given Magnus-type ordering. -/
theorem projection_compatible {k : ℕ} {G : Type*} [Group G] {F : Fin k → Type*} [∀ j, Group (F j)]
    (W : AlmostDirectProductWorld k G F) :
    ∀ (j : Fin k) (f : F j), f ∈ W.cone j →
      embedFactor W j f ∈ lexCone W ∧ W.nf (embedFactor W j f) j = f := by sorry

end PCB
