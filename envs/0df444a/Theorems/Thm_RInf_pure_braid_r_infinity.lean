-- Prove2me | Theorems.Thm_RInf_pure_braid_r_infinity
-- name    : RInf.pure_braid_r_infinity
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-22T00:30:32.961901+00:00
-- url     : https://prove2.me/theorems/1e764e40-66b3-4fc2-8b85-b61c997c4bb7
-- title:
--   The pure Artin braid groups on at least five strings have the R-infinity property (Theorem 12)
-- statement:
--   The pure Artin braid group on n strings has the R-infinity property for every n of at least five: every automorphism of the braid group has infinite Reidemeister number. The automorphism acts on the commutator layer with the eigenvalue one, hence with infinite Reidemeister number on the layer, and the transfer carries the infinitude to the Reidemeister number of the automorphism itself. The cases of three and four strings are treated separately in the paper and are pruned from this mission.
-- source:
--   K. Dekimpe, D. L. Goncalves, O. Ocampo, The R-infinity property for pure Artin braid groups, Monatshefte fur Mathematik 195 (2021) 15-33, Section 3.2 (Theorem 12).

import Mathlib
import Definitions.Def_RInf_alg
import Definitions.Def_RInf_braid

namespace RInf

/-!  The goal (Theorem 12): every pure Artin braid group on at least five
strings has the R-infinity property. Every automorphism α of the braid group
acts on the commutator layer with the eigenvalue one by milestone 5, hence
with infinite Reidemeister number on the layer by milestone 6, and the
transfer of the world carries the infinitude to the Reidemeister number of α
itself, by the reductions of milestones 1 and 7. The cases of three and four
strings are treated separately in the paper and are pruned from this
mission. -/
theorem pure_braid_r_infinity {n : Nat} {P Q : Type*} [Group P] [AddCommGroup Q]
    (W : BraidWorld n P Q) (hn : 5 ≤ n) : RInfinity P := by sorry

end RInf
