-- Prove2me | Theorems.Thm_PCB_torsion_free
-- name    : PCB.torsion_free
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-22T20:09:29.347505+00:00
-- url     : https://prove2.me/theorems/bec733e9-a5df-47bb-9e7e-bfd70fe39ef0
-- title:
--   Almost-direct products of free groups are torsion-free without generalized torsion (Corollary 5)
-- statement:
--   An almost-direct product of free groups is torsion-free and has no generalized torsion. Once the goal equips the group with a bi-invariant ordering, the standard consequences follow: no positive power of a non-identity element is trivial, and no product of conjugates of a non-identity element is trivial, since such products are positive in any bi-invariant ordering. This is Corollary 5 of the paper.
-- source:
--   O. Ocampo, J. R. T. Theodoro de Lima, Positive cones and bi-orderings on almost-direct products of free groups, arXiv:2209.04706 (2022), Section 2 (Corollary 5, the torsion statements).

import Mathlib
import Definitions.Def_PCB_alg
import Definitions.Def_PCB_tor

namespace PCB

/-!  Milestone 4 (Corollary 5): an almost-direct product of free groups is
torsion-free and has no generalized torsion. By the goal, the group admits
a bi-invariant ordering, and bi-orderable groups are torsion-free and
admit no nontrivial product of conjugates of a single element. -/
theorem torsion_free {k : ℕ} {G : Type*} [Group G] {F : Fin k → Type*} [∀ j, Group (F j)]
    (W : AlmostDirectProductWorld k G F) :
    TorsionFreeNoGeneralizedTorsion G := by sorry

end PCB
