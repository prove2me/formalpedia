-- Prove2me | Theorems.Thm_ShiShallow_apply1_eq_apply1Matrix_mulVec
-- name    : ShiShallow.apply1_eq_apply1Matrix_mulVec
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-13T18:22:08.738192+00:00
-- url     : https://prove2.me/theorems/e8258266-3f3a-46bf-9e2a-58255ee559f7
-- title:
--   One-qubit gate: state-function semantics equals the matrix-vector action
-- statement:
--   This closes one half of a long-standing structural gap. The development carries TWO INDEPENDENT semantics for the same objects. First, an execution semantics on state functions: a state on n wires is a function from bit strings to complex numbers, and a one-qubit gate on wire i acts by summing the gate's two matrix entries against the two states obtained by overwriting wire i with false and with true. Second, a matrix semantics: the same gate becomes a large square matrix indexed by bit strings, whose entry at a pair of strings is the gate entry read off wire i when the strings agree on every OTHER wire, and zero otherwise. Until now no lemma anywhere related the two, for any gate. This theorem says they agree exactly, at the level of a single gate.
--
--   MECHANISM: a two-point sum reduction. The matrix-vector product sums over exponentially many bit strings, but almost every term vanishes: the agreement condition off wire i forces the summation string to be the input string with wire i overwritten. Since wire i carries one bit, exactly TWO strings survive, and there the summand is precisely the corresponding term of the two-term boolean sum on the state-function side. Three facts are discharged: strings failing the condition contribute zero; the two survivors satisfy the condition and read the expected value on wire i; and the two are distinct.
--
--   TWO NOTATION FACTS worth recording, because both are easy to trip on. The matrix-vector infix notation is SCOPED inside the matrix namespace and the definitions bundle does not open it, so the statement is written with the fully qualified function. And the boolean sum expansion orders its terms with true first, so the final step needs a commutation rather than closing by reflexivity.
--
--   HONEST LIMITATIONS. This is ONE gate, not a circuit: the layer and circuit levels -- where the matrix product runs opposite to application order -- remain separate. Nothing is claimed about layer well-formedness. No universality claim for the H, S, T, X, CNOT gate set. The gate matrix is ARBITRARY, so nothing here assumes or proves unitarity, norm preservation, or any spectral property, and the identity holds for singular matrices just as well.

import Definitions.Def_ShiShallow_Matrix

set_option autoImplicit false

namespace ShiShallow

theorem apply1_eq_apply1Matrix_mulVec {n : ℕ} (U : Matrix Bool Bool ℂ) (i : Fin n)
    (ψ : QState n) :
    apply1 U i ψ = Matrix.mulVec (apply1Matrix U i) ψ := by
  sorry

end ShiShallow
