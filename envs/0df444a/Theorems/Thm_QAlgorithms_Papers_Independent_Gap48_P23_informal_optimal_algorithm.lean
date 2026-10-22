-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_informal_optimal_algorithm
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.informal_optimal_algorithm
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:26:55.332781+00:00
-- url     : https://prove2.me/theorems/8ade9e8f-3452-4c21-bb16-4a9f0c41c74b
-- title:
--   Theorem 1.1 (informal).
-- statement:
--   Work in finite-dimensional complex Hilbert spaces with the indicated computational bases. A channel is a fixed completely positive trace-preserving map, independent of the unknown word $x$ and common basis $U$. Write $\rho_x^U=U^{\otimes n}|x\rangle\langle x|U^{\dagger\otimes n}$. For an input promise $P$, let $F_{f,P}(\Phi)$ be the minimum of $\langle f(x)|U^\dagger\Phi(\rho_x^U)U|f(x)\rangle$ over every allowed $x$ and $U\in U(d)$, and let $F_{f,P}$ be its supremum over channels. An omitted $P$ means all words. Boolean functions use $d=2$; positive odd $n$ is imposed whenever symmetry and equivariance of a Boolean function are required.
--
--   For every positive odd $n$ and symmetric equivariant Boolean $f$, there are interpolation parameters $0\le t_k\le1$ for which Algorithm 2 is optimal. Its optimal fidelity and parameters are the attained optimum of the explicit LP with $\lfloor n/2\rfloor+2$ variables and $3\lfloor n/2\rfloor+3$ inequalities. With real rotations supplied as exact single-qubit gates,
--   $$\operatorname{size}(A_t)\le Cn^4\log n\qquad(n\ge N).$$
--   The constants $C>0,N$ precede $n,f,t$ and the fixed permitted coefficient family. This combines the precise contents of Theorems 4.6–4.8, without a finite-precision computation claim about arbitrary real numbers.
--
--   This is the stated interface for the corresponding result of the paper.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 5, Theorem 1.1 (informal).

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

/-- PDF p.5, Theorem 1.1 (informal), interpreted through Theorems 4.6-4.8:
optimal template, attained explicit LP of linear size, and the exact continuous
one-qubit/CNOT gate bound, with universal constants. -/
theorem informal_optimal_algorithm :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, 1 ≤ n → Odd n →
      ∀ (alpha : RealSchurCoefficients n), LawfulCoefficients alpha →
      ∀ f : Word n 2 → Fin 2, WordSymmetric f → Equivariant f →
        ∃ t : TwoRowShape n → ℝ, FunctionLPFeasible f (optimalFunctionFidelity (fun _ => True) f) t ∧
          IsFunctionOptimal (fun _ => True) f (template alpha t) ∧
          (∀ c s, FunctionLPFeasible f c s → c ≤ optimalFunctionFidelity (fun _ => True) f) ∧
          (n ≥ N → ∃ circuit : OneOutputCircuit n,
            circuitOutput circuit (wordBinaryEmbedding n) = template alpha t ∧
            (circuit.circuit.size : ℝ) ≤ C * (n:ℝ)^4 * Real.log n) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
