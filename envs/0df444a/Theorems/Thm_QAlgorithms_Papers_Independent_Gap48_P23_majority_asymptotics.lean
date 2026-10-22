-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_majority_asymptotics
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.majority_asymptotics
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:25:59.079999+00:00
-- url     : https://prove2.me/theorems/b920b4a6-3eb5-4260-9352-02960b365c6b
-- title:
--   Quantum majority vote: Theorem 1.2
-- statement:
--   Work in finite-dimensional complex Hilbert spaces with the indicated computational bases. A channel is a fixed completely positive trace-preserving map, independent of the unknown word $x$ and common basis $U$. Write $\rho_x^U=U^{\otimes n}|x\rangle\langle x|U^{\dagger\otimes n}$. For an input promise $P$, let $F_{f,P}(\Phi)$ be the minimum of $\langle f(x)|U^\dagger\Phi(\rho_x^U)U|f(x)\rangle$ over every allowed $x$ and $U\in U(d)$, and let $F_{f,P}$ be its supremum over channels. An omitted $P$ means all words. Boolean functions use $d=2$; positive odd $n$ is imposed whenever symmetry and equivariance of a Boolean function are required.
--
--   For positive odd $n$, optimal quantum majority has the asymptotics
--   $$F_{\rm MAJ}(n)=\tfrac12+\Theta(n^{-1/2}).$$
--   For each $q\in\{3,6\}$, let $P_q$ require minority weight at most $\lfloor n/q\rfloor$. Then
--   $$1-F_{{\rm MAJ},P_q}(n)=\Theta(n^{-1}).$$
--   Each $\Theta$ means positive lower and upper constants and a threshold chosen before $n$. The $q=3$ clause is the abstract and proof promise; $q=6$ separately preserves the stronger printed promise. These are worst-case statements, including the all-equal inputs without claiming their pointwise error is nonzero.
--
--   This is the stated interface for the corresponding result of the paper.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 1, Quantum majority vote: Theorem 1.2

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

/-- PDF pp.1,5,37-38, Theorem 1.2. PRINTED promise: ||x|-n/2|>=n/3.
CHANGED main promise to minority<=floor(n/3), as in abstract and proof; retain
minority<=floor(n/6) as a separate companion. WHY: the printed formula means a
five-sixths majority. These are worst-case, not pointwise, asymptotics.
Independent moderation of this source correction is required. -/
theorem majority_asymptotics :
    (∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∃ N : ℕ, ∀ n ≥ N, 1 ≤ n → Odd n →
      a / Real.sqrt n ≤ optimalFunctionFidelity (fun _ => True) (majority n) - 1/2 ∧
      optimalFunctionFidelity (fun _ => True) (majority n) - 1/2 ≤ b / Real.sqrt n) ∧
    (∀ q ∈ ({3, 6} : Finset ℕ), ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∃ N : ℕ,
      ∀ n ≥ N, 1 ≤ n → Odd n →
        a / n ≤ 1 - optimalFunctionFidelity (majorityPromise n q) (majority n) ∧
        1 - optimalFunctionFidelity (majorityPromise n q) (majority n) ≤ b / n) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
