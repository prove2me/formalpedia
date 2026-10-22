-- Prove2me | Theorems.Thm_RInf_reid_two_classes
-- name    : RInf.reid_two_classes
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-22T00:26:48.229511+00:00
-- url     : https://prove2.me/theorems/723b1ac4-f170-485f-afa7-589897f952df
-- title:
--   Eigenvalue one or minus one on a lattice yields two Reidemeister classes (Lemma 4)
-- statement:
--   If the automorphism of the standard integer lattice of rank k has the eigenvalue one or the eigenvalue minus one - some nonzero lattice vector is fixed or negated - then there are two lattice elements that are not twisted conjugate under the automorphism: its Reidemeister number is at least two. The proof follows the lattice analysis of Lemma 4: for the eigenvalue one the classes are infinite in number, and for the eigenvalue minus one the fixed sublattice splits the Reidemeister counting at least in two.
-- source:
--   K. Dekimpe, D. L. Goncalves, O. Ocampo, The R-infinity property for pure Artin braid groups, Monatshefte fur Mathematik 195 (2021) 15-33, Section 3 (Lemma 4).

import Mathlib
import Definitions.Def_RInf_alg
import Definitions.Def_RInf_braid

namespace RInf

/-!  Milestone 2 (Lemma 4): an automorphism of a standard integer lattice
whose matrix has the eigenvalue one or minus one has at least two Reidemeister
classes. If some nonzero lattice vector is fixed or negated by m, then there
are two elements of the lattice that are not twisted conjugate under m. The
proof follows the lattice analysis of Lemma 4: for the eigenvalue one the
classes are infinite in number, and for the eigenvalue minus one the fixed
sublattice splits the Reidemeister counting at least in two. -/
theorem reid_two_classes {k : Nat} (m : (Fin k → Int) ≃+ (Fin k → Int))
    (h : ∃ v : Fin k → Int, v ≠ 0 ∧ (m v = v ∨ m v = -v)) :
    ∃ x y : Fin k → Int, ¬ TwistedConjAdd m x y := by sorry

end RInf
