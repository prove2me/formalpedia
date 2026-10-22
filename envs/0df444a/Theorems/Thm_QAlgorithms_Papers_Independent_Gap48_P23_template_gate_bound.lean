-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_template_gate_bound
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.template_gate_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:43:43.818068+00:00
-- url     : https://prove2.me/theorems/0c8fdbf1-2404-48f6-b051-4b3e717d58b5
-- title:
--   Theorem 4.8.
-- statement:
--   Work in finite-dimensional complex Hilbert spaces with the indicated computational bases. A channel is a fixed completely positive trace-preserving map, independent of the unknown word $x$ and common basis $U$. Write $\rho_x^U=U^{\otimes n}|x\rangle\langle x|U^{\dagger\otimes n}$. For an input promise $P$, let $F_{f,P}(\Phi)$ be the minimum of $\langle f(x)|U^\dagger\Phi(\rho_x^U)U|f(x)\rangle$ over every allowed $x$ and $U\in U(d)$, and let $F_{f,P}$ be its supremum over channels. An omitted $P$ means all words. Boolean functions use $d=2$; positive odd $n$ is imposed whenever symmetry and equivariance of a Boolean function are required.
--
--   With all one-qubit gates and CNOT available, there are universal $C>0,N$ such that, for every positive odd $n\ge N$ and every allowed real interpolation vector, the full template channel has an exact gate-list realization with
--   $$\operatorname{size}(A_t)\le Cn^4\log n.$$
--   The realization initializes zero ancillas, applies gates on named wires, retains one qubit, and traces the rest. Equality is on all operators.
--
--   This is the stated interface for the corresponding result of the paper.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 33, Theorem 4.8.

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P23

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P23

open MeasureTheory

open scoped ComplexConjugate Matrix ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Exact frozen coordinate helpers; no paper-local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

/-- PDF p.33, Theorem 4.8: constants are uniform over n and all real rotation
parameters. Exact continuous gates are assumed as in the source proof; no
finite-precision Turing computation of arbitrary real constants is asserted. -/
theorem template_gate_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N, 1 ≤ n → Odd n →
      ∀ (alpha : RealSchurCoefficients n), LawfulCoefficients alpha →
      ∀ t : TwoRowShape n → ℝ, (∀ k, 0 ≤ t k ∧ t k ≤ 1) →
        ∃ circuit : OneOutputCircuit n,
          circuitOutput circuit (wordBinaryEmbedding n) = template alpha t ∧
          (circuit.circuit.size : ℝ) ≤ C * (n:ℝ)^4 * Real.log n := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
