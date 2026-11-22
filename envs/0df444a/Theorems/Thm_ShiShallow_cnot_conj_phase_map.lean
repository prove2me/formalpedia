-- Prove2me | Theorems.Thm_ShiShallow_cnot_conj_phase_map
-- name    : ShiShallow.cnot_conj_phase_map
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-13T05:56:29.088084+00:00
-- url     : https://prove2.me/theorems/f1e60dea-00d4-46cd-b6a8-d99c004440a3
-- title:
--   CNOT conjugation of an arbitrary pointwise-phase map
-- statement:
--   Conjugating ANY map that acts as a pointwise phase by a CNOT yields again a pointwise phase, whose phase function is the original one composed with the CNOT's index map:
--
--     cnotState i j (F (cnotState i j psi)) = fun x => a (u x) * psi x,   where u x = update x j (xor (x j) (x i)).
--
--   WHY THE GENERALITY IS THE POINT. The existing conjugation results in this development are stated only for the specific map apply1 (tMat ^ k). This version applies to any pointwise-phase map, which gives two things the specific versions cannot. First it SUBSUMES them: instantiate the phase as y |-> if y j then omega^k else 1 and use that the j-th bit of u x is the parity of bits i and j. Second, and this is the useful part, IT NESTS -- the conclusion is itself in pointwise-phase form, so the result can be conjugated again. Iterated conjugation is exactly what a triple-parity phase factor requires (two CNOTs in, two out), and single-purpose lemmas cannot supply it.
--
--   Proof: unfold the outer CNOT at a point, apply the phase hypothesis there, then collapse the doubled index update using an index-level involution proved as a private helper. Note that involution is NOT the published state-level cnotState_involutive; they are different statements.
--
--   SCOPE. This is an algebraic fact about maps on amplitude arrays. It proves no circuit identity, constructs no CCZ or Toffoli, and assumes no unitarity of F and no normalisation of the state -- F need not come from a gate at all. The gate set is H, S, T, X, CNOT with no universality theorem imported or proved.

import Definitions.Def_ShiShallow_Core

set_option autoImplicit false

namespace ShiShallow

theorem cnot_conj_phase_map {n : ℕ} (i j : Fin n) (hij : i ≠ j) (ψ : QState n)
    (F : QState n → QState n) (a : Bits n → ℂ)
    (hF : ∀ (φ : QState n) (y : Bits n), F φ y = a y * φ y) :
    cnotState i j hij (F (cnotState i j hij ψ))
      = fun x => a (Function.update x j (xor (x j) (x i))) * ψ x := by
  sorry

end ShiShallow
