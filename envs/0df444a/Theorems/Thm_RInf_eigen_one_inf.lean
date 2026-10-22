-- Prove2me | Theorems.Thm_RInf_eigen_one_inf
-- name    : RInf.eigen_one_inf
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-22T00:27:32.528606+00:00
-- url     : https://prove2.me/theorems/af06d29f-78cd-46fe-9ff4-dcc43c229d45
-- title:
--   An automorphism of a lattice with the eigenvalue one has infinite Reidemeister number (Lemma 4)
-- statement:
--   If the automorphism of the standard integer lattice of rank k has the eigenvalue one - some nonzero vector is fixed - then its Reidemeister number is infinite. On the abelian lattice the twisted conjugacy classes are the cosets of the image of the map taking z to z minus the image of z under the automorphism, and the index of this image is infinite because the determinant of one minus the automorphism vanishes at the eigenvalue one.
-- source:
--   K. Dekimpe, D. L. Goncalves, O. Ocampo, The R-infinity property for pure Artin braid groups, Monatshefte fur Mathematik 195 (2021) 15-33, Section 3 (Lemma 4, eigenvalue-one refinement).

import Mathlib
import Definitions.Def_RInf_alg
import Definitions.Def_RInf_braid

namespace RInf

/-!  Milestone 3 (Lemma 4, eigenvalue-one refinement): an automorphism of a
standard integer lattice with the eigenvalue one has infinite Reidemeister
number. If some nonzero vector is fixed by m, the Reidemeister number of m is
infinite: on the abelian lattice the twisted conjugacy classes are the
cosets of the image of the map taking z to z minus m z, whose determinant
vanishes at the eigenvalue one, so the index of the image is infinite. -/
theorem eigen_one_inf {k : Nat} (m : (Fin k → Int) ≃+ (Fin k → Int))
    (h : HasEigenOne m) : ReidInfAdd m := by sorry

end RInf
