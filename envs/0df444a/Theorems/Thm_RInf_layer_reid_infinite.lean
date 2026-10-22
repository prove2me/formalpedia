-- Prove2me | Theorems.Thm_RInf_layer_reid_infinite
-- name    : RInf.layer_reid_infinite
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-22T00:29:27.34724+00:00
-- url     : https://prove2.me/theorems/10601428-7c21-4686-8efb-32aeea8bbf25
-- title:
--   The induced action on the commutator layer has infinite Reidemeister number (Section 3.2)
-- statement:
--   Every automorphism of the pure Artin braid group acts on the commutator layer with infinite Reidemeister number. By the eigenvalue-one theorem the induced action of the automorphism on the layer has the eigenvalue one; transported along the standard coordinates of the layer, the lattice criterion yields infinitely many pairwise non-twisted-conjugate elements of the layer. This is the statement of Section 3.2 from which the main theorem follows by the transfer of Remark 1.
-- source:
--   K. Dekimpe, D. L. Goncalves, O. Ocampo, The R-infinity property for pure Artin braid groups, Monatshefte fur Mathematik 195 (2021) 15-33, Section 3.2.

import Mathlib
import Definitions.Def_RInf_alg
import Definitions.Def_RInf_braid

namespace RInf

/-!  Milestone 6: the induced action on the commutator layer has infinite
Reidemeister number. By milestone 5 the induced action of α on the layer has
the eigenvalue one; transporting along the standard coordinates of the layer
and applying the eigenvalue-one criterion of milestone 3, the Reidemeister
number of the induced automorphism of the layer is infinite. This is the
statement R of the second induced action is infinite of Section 3.2, from
which the main theorem follows by the transfer of Remark 1. -/
theorem layer_reid_infinite {n : Nat} {P Q : Type*} [Group P] [AddCommGroup Q]
    (W : BraidWorld n P Q) (α : P ≃* P) : ReidInfAdd (W.act α) := by sorry

end RInf
