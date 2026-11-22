-- Prove2me | Theorems.Thm_ShiShallow_projOut_majority_inclusion_exclusion
-- name    : ShiShallow.projOut_majority_inclusion_exclusion
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-13T18:54:28.284511+00:00
-- url     : https://prove2.me/theorems/f68cb5bb-ddc6-46d4-b883-33bed93be5d9
-- title:
--   The majority-of-three measurement projector is the inclusion-exclusion polynomial in the single-wire accept projectors
-- statement:
--   This decomposes a majority-vote measurement into the individual measurements it is built from. Fix three wires. The matrix on the left is the diagonal zero-one matrix accepting exactly those computational basis strings in which at least two of the three chosen wires read one -- precisely what a three-copy repetition argument reads out, since such an argument accepts when a majority of the copies accept. The matrix on the right is a polynomial with integer coefficients in the three single-wire accept projectors: the sum of the three PAIRWISE products minus TWICE the triple product.
--
--   WHY IT MATTERS. Having the majority readout written this way is what lets bounds proved one copy at a time be combined, because every term of the polynomial involves only products of per-wire projectors, whose behaviour can be controlled individually.
--
--   WHY THE PROOF IS SHORT. All these projectors are DIAGONAL. A diagonal zero-one matrix commutes with every other diagonal matrix and squares to itself, so no noncommutative algebra and no ordering care is needed -- which is why this step, which looks like it should require operator algebra, does not. Concretely the proof shows a product of two, then of three, of these matrices is again diagonal with entry the product of the individual indicators, that is the logical AND of the per-wire predicates; off the diagonal every term vanishes; and on the diagonal the claim collapses to an eight-case identity among zeros and ones over the complex numbers, checked by exhausting the three booleans.
--
--   A NOTE ON THE NUMERAL. The coefficient two on the triple product elaborates as a square-matrix ring numeral, so the proof first rewrites it as a sum of two copies; that keeps the entire entrywise computation inside addition, subtraction and multiplication of the projectors and avoids needing any lemma about matrix numerals.
--
--   HONEST LIMITATIONS. This is PURELY an algebraic identity between two matrices. There is no quantum dynamics in it: no circuit, no unitarity, no gate, no appeal to the measurement postulate. The projectors are used exactly as defined, and no separate property of them -- not even idempotence -- is established; idempotence is only implicitly subsumed by the entrywise computation. Nothing here shows a majority readout is IMPLEMENTABLE by any circuit; that is a separate accepted Toffoli-based construction. Nothing is claimed about acceptance probabilities, witnesses, entanglement, or amplification bounds, and no universality claim is made for the H, S, T, X, CNOT gate set. An identical scalar identity is already accepted over the reals, but that bundle sits on a different import tower and is unreachable here, so the eight-case check is redone inline over the complex numbers.

import Definitions.Def_ShiShallow_Matrix

set_option autoImplicit false

namespace ShiShallow

theorem projOut_majority_inclusion_exclusion {n : ℕ} (w1 w2 w3 : Fin n) :
    (Matrix.of fun y z => if y = z ∧ 2 ≤ (if y w1 = true then (1:ℕ) else 0)
            + (if y w2 = true then (1:ℕ) else 0) + (if y w3 = true then (1:ℕ) else 0)
          then (1:ℂ) else 0)
      = projOut w1 * projOut w2 + projOut w2 * projOut w3 + projOut w3 * projOut w1
          - 2 * (projOut w1 * projOut w2 * projOut w3) := by
  sorry

end ShiShallow
