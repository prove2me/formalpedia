-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P03_wire_permutation
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P03.wire_permutation
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T03:51:30.316047+00:00
-- url     : https://prove2.me/theorems/b12c00b6-20f8-43e2-9198-9a95af8f9392
-- title:
--   §2.2 Corollaries, item 1: wire permutation
-- statement:
--   For any permutation $\pi$ of the $n$ wire positions, there is a CNOT operation sequence with clean auxiliary work that performs the corresponding bit permutation using at most $4n$ gates:
--
--   $$
--   |x,0\rangle\longmapsto |x\circ\pi^{-1},0\rangle.
--   $$
--
--   The assertion includes $n=0$, when the empty computation is the identity. It concerns wire positions, rather than arbitrary permutations of Boolean words.
-- source:
--   Quantum measurements and the Abelian Stabilizer Problem, arXiv:quant-ph/9511026v1, PDF p. 8, §2.2 Corollaries, item 1: wire permutation

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P03

noncomputable section

open scoped Matrix ComplexConjugate Kronecker

namespace QAlgorithms.Papers.Independent.Intakethird100.P03

open QAlgorithms.Papers.Independent.Renew46.P01 (cleanVector)

attribute [local instance] Classical.propDecidable

/-- PDF p.8, Corollary 1: permutation of wire positions, with clean work; the source's
4n is an upper bound on actual CNOT applications. The n=0 case is the identity. -/
theorem wire_permutation (n : ℕ) (p : Equiv.Perm (Fin n)) :
    ∃ (w : ℕ) (c : Circuit {Gate.ofMatrix2 cnot} (n + w)),
      c.size ≤ 4 * n ∧ ∀ x : Qubits n,
        act c.unitary (inputState x w) = inputState (fun i => x (p.symm i)) w := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P03

end
