-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P46_theoremB_1
-- name    : QAlgorithms.Papers.Independent.Extend50.P46.theoremB_1
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:10:22.456182+00:00
-- url     : https://prove2.me/theorems/5f974c01-34b4-4c78-a3e1-34cef72b47a3
-- title:
--   Learning transfer matrices in an arbitrary Hermitian operator basis
-- statement:
--   The unknown channel is an arbitrary complex-linear CPTP map on $n$ qubits. Choi access supplies independent copies of the normalized reference-first state $J(\mathcal N)=(\mathrm{id}\otimes\mathcal N)(|\Omega\rangle\langle\Omega|)$. The algorithm is a joint POVM on exactly its stated number of copies, chosen before the channel. Accuracy means simultaneous absolute error under its actual Born law. All constants, and all exponents hidden in $\widetilde O$, are uniform before the channel, dimension, basis and accuracy parameters. Assume $\varepsilon>0$ and $0<\delta<1$.
--
--   Here $n\ge0$ is the number of qubits, $d=2^n$, states are positive semidefinite matrices of trace one, and $\mathcal N$ is a complex-linear CPTP map. The basis $Q=(Q_i)_{i=1}^{d^2}$ is a complete Hermitian Hilbert–Schmidt orthonormal basis. Write $R^Q_{ij}=\operatorname{tr}(Q_i\mathcal N(Q_j))$, $a_i=\operatorname{tr}(Q_i\rho)$ and $b_i=\operatorname{tr}(Q_iO)$. The norm $\|\cdot\|_2$ is the Hilbert–Schmidt norm, and $q=\max_i\|Q_i\|_\infty$ uses the spectral norm.
--
--   There is a learner using
--
--   $$m=\widetilde O\!\left(\frac{n^3+n\log(1/\delta)}{\varepsilon^4}(2^nq^2)^4\right)$$
--
--   copies and returning a table $\widehat R$ such that $|\widehat R_{ij}-R^Q_{ij}|\le\varepsilon$ simultaneously for every pair, with probability at least $1-\delta$.
--
--   No unitary or tensor-product promise is made on $Q$, and there is no classical storage or time bound. The soft factor is a fixed power of floored logarithms of the listed parameters.
-- source:
--   Learning Quantum Processes and Hamiltonians via the Pauli Transfer Matrix, arXiv:2212.04471v2, PDF p. 39, Theorem B.1

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P46

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P46

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.39-40, Theorem B.1. Uniform soft-O constants and exponent precede
n and Q. Q is any complete Hermitian ONB, with no unitarity assumption. -/
theorem theoremB_1 :
    ∃ C : ℝ, 0 < C ∧ ∃ p : ℕ, ∀ n : ℕ, ∀ Q : HermitianBasis n,
      ∀ eps delta : ℝ, 0 < eps → 0 < delta → delta < 1 →
      ∃ P : ChoiLearner n (Matrix (Fin (4 ^ n)) (Fin (4 ^ n)) ℝ),
        (P.copies : ℝ) ≤ C * generalCost Q eps delta *
          softFactor p n eps delta ((2 : ℝ)^n * basisNorm Q ^ 2) ∧
        ∀ N : {F : (Matrix (Qubits n) (Qubits n) ℂ) →ₗ[ℂ] (Matrix (Qubits n) (Qubits n) ℂ) // IsChannel F},

          1 - delta ≤ choiReportEventProbability P N {r | tableGood r (tm Q N) eps} := by sorry

end QAlgorithms.Papers.Independent.Extend50.P46

end
