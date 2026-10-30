-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P46_lemmaB_5
-- name    : QAlgorithms.Papers.Independent.Extend50.P46.lemmaB_5
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:12:03.118209+00:00
-- url     : https://prove2.me/theorems/45810038-5c78-4ba4-86c9-3a3289962c16
-- title:
--   Discovering significant transfer-matrix entries in a general basis
-- statement:
--   The unknown channel is an arbitrary complex-linear CPTP map on $n$ qubits. Choi access supplies independent copies of the normalized reference-first state $J(\mathcal N)=(\mathrm{id}\otimes\mathcal N)(|\Omega\rangle\langle\Omega|)$. The algorithm is a joint POVM on exactly its stated number of copies, chosen before the channel. Accuracy means simultaneous absolute error under its actual Born law. All constants, and all exponents hidden in $\widetilde O$, are uniform before the channel, dimension, basis and accuracy parameters. Assume $\varepsilon>0$ and $0<\delta<1$.
--
--   Here $n\ge0$ is the number of qubits, $d=2^n$, states are positive semidefinite matrices of trace one, and $\mathcal N$ is a complex-linear CPTP map. The basis $Q=(Q_i)_{i=1}^{d^2}$ is a complete Hermitian Hilbert–Schmidt orthonormal basis. Write $R^Q_{ij}=\operatorname{tr}(Q_i\mathcal N(Q_j))$, $a_i=\operatorname{tr}(Q_i\rho)$ and $b_i=\operatorname{tr}(Q_iO)$. The norm $\|\cdot\|_2$ is the Hilbert–Schmidt norm, and $q=\max_i\|Q_i\|_\infty$ uses the spectral norm.
--
--   For a channel with at most $s$ nonzero $Q$-TM entries and unknown support, a learner uses
--
--   $$m=\widetilde O\!\left(\frac{n^3+n\log(1/\delta)}{\varepsilon^4}(2^nq^2)^4\right).$$
--
--   With probability at least $1-\delta$, the finite list of retained estimates has all four properties: omitted true entries have magnitude at most $\varepsilon$; listed true entries have magnitude greater than $\varepsilon/6$; the list has length at most $s$; and each listed estimate has absolute error at most $\varepsilon$.
--
--   The list is constructed by a strict $\varepsilon/2$ cutoff on preliminary estimates. No support is supplied to the algorithm.
-- source:
--   Learning Quantum Processes and Hamiltonians via the Pauli Transfer Matrix, arXiv:2212.04471v2, PDF p. 41, Lemma B.5

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P46

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P46

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.41, Lemma B.5: support discovery in an arbitrary Hermitian ONB,
with all four list guarantees and the same general-basis sample bound. -/
theorem lemmaB_5 :
    ∃ C : ℝ, 0 < C ∧ ∃ p : ℕ, ∀ n s : ℕ, ∀ Q : HermitianBasis n,
      ∀ eps delta : ℝ, 0 < eps → 0 < delta → delta < 1 →
      ∃ P : ChoiLearner n (Matrix (Fin (4 ^ n)) (Fin (4 ^ n)) ℝ),
        (P.copies : ℝ) ≤ C * generalCost Q eps delta *
          softFactor p n eps delta ((2 : ℝ)^n * basisNorm Q ^ 2) ∧
        ∀ N : {F : (Matrix (Qubits n) (Qubits n) ℂ) →ₗ[ℂ] (Matrix (Qubits n) (Qubits n) ℂ) // IsChannel F},
          supportCount (fun ij : Fin (4 ^ n) × Fin (4 ^ n) => tm Q N ij.1 ij.2) ≤ s →

          1 - delta ≤ choiReportEventProbability P N {r | sparseListGood r (tm Q N) eps s} := by sorry

end QAlgorithms.Papers.Independent.Extend50.P46

end
