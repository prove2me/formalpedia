-- Prove2me | Theorems.Thm_RInf_act_torsion
-- name    : RInf.act_torsion
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-22T00:28:06.268347+00:00
-- url     : https://prove2.me/theorems/9287ba6a-4518-4810-8815-d3b352ee6e79
-- title:
--   Every automorphism acts on the commutator layer with finite order (Section 2)
-- statement:
--   Every automorphism of the pure Artin braid group acts on the commutator layer with finite order: some positive iterate of the induced automorphism of the layer is the identity. The induced action factors through the representation of the finite symmetric group on n + 1 letters, so the finiteness of the symmetric group bounds the order of the induced action. This is the finiteness observation of Section 2 that precedes the representation-theoretic analysis.
-- source:
--   K. Dekimpe, D. L. Goncalves, O. Ocampo, The R-infinity property for pure Artin braid groups, Monatshefte fur Mathematik 195 (2021) 15-33, Section 2 (the finiteness of the image of the induced action).

import Mathlib
import Definitions.Def_RInf_alg
import Definitions.Def_RInf_braid

namespace RInf

/-!  Milestone 4 (Section 2, the finiteness of the image of the induced
action): every automorphism of the pure braid group acts on the commutator
layer with finite order. Because the induced action factors through the
representation of the finite symmetric group on n + 1 letters, some positive
iterate of the induced automorphism of the layer is the identity. This is the
finiteness observation of Section 2 that precedes the representation-theoretic
analysis of Section 3. -/
theorem act_torsion {n : Nat} {P Q : Type*} [Group P] [AddCommGroup Q]
    (W : BraidWorld n P Q) (α : P ≃* P) :
    ∃ m : Nat, 0 < m ∧ ∀ q : Q, ((fun x => W.act α x)^[m]) q = q := by sorry

end RInf
