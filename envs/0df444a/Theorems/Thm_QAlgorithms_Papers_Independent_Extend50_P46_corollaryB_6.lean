-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P46_corollaryB_6
-- name    : QAlgorithms.Papers.Independent.Extend50.P46.corollaryB_6
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:12:55.834468+00:00
-- url     : https://prove2.me/theorems/c35cadda-8577-43b1-937e-5bd69a14d8b1
-- title:
--   Arbitrary-state prediction for a sparse general transfer matrix
-- statement:
--   The unknown channel is an arbitrary complex-linear CPTP map on $n$ qubits. Choi access supplies independent copies of the normalized reference-first state $J(\mathcal N)=(\mathrm{id}\otimes\mathcal N)(|\Omega\rangle\langle\Omega|)$. The algorithm is a joint POVM on exactly its stated number of copies, chosen before the channel. Accuracy means simultaneous absolute error under its actual Born law. All constants, and all exponents hidden in $\widetilde O$, are uniform before the channel, dimension, basis and accuracy parameters. Assume $\varepsilon>0$ and $0<\delta<1$.
--
--   Here $n\ge0$ is the number of qubits, $d=2^n$, states are positive semidefinite matrices of trace one, and $\mathcal N$ is a complex-linear CPTP map. The basis $Q=(Q_i)_{i=1}^{d^2}$ is a complete Hermitian Hilbert–Schmidt orthonormal basis. Write $R^Q_{ij}=\operatorname{tr}(Q_i\mathcal N(Q_j))$, $a_i=\operatorname{tr}(Q_i\rho)$ and $b_i=\operatorname{tr}(Q_iO)$. The norm $\|\cdot\|_2$ is the Hilbert–Schmidt norm, and $q=\max_i\|Q_i\|_\infty$ uses the spectral norm.
--
--   Fix $s\ge1$ and $B>0$. For a channel with at most $s$ nonzero $Q$-TM entries and unknown support, there is a learner using
--
--   $$m=\widetilde O\!\left(\frac{n^3+n\log(1/\delta)}{\varepsilon^4}B^4s^4(\sqrt{2^n}q)^{12}\right)$$
--
--   copies. Its classical table predicts every $\operatorname{tr}(O\mathcal N(\rho))$ within $\varepsilon$, simultaneously over all states and all Hermitian $O$ with $\|O\|_2\le B\sqrt{2^n}$, on an event of probability at least $1-\delta$.
--
--   The predictor is a fixed coefficient contraction. There is no state sparsity, observable sparsity, or efficient classical evaluation-time assertion.
-- source:
--   Learning Quantum Processes and Hamiltonians via the Pauli Transfer Matrix, arXiv:2212.04471v2, PDF p. 41, Corollary B.6

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P46

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P46

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.41, Corollary B.6: sparse unknown TM, arbitrary state and bounded
observable, with no support advice or classical evaluation-time bound. -/
theorem corollaryB_6 :
    ∃ C : ℝ, 0 < C ∧ ∃ p : ℕ, ∀ n s : ℕ, 1 ≤ s → ∀ Q : HermitianBasis n,
      ∀ B eps delta : ℝ, 0 < B → 0 < eps → 0 < delta → delta < 1 →
      ∃ P : ChoiLearner n (Matrix (Fin (4 ^ n)) (Fin (4 ^ n)) ℝ),
        (P.copies : ℝ) ≤ C * ((n : ℝ)^3 + n * Real.log delta⁻¹) / eps^4 *
          B^4 * (s : ℝ)^4 * (Real.sqrt ((2 : ℝ)^n) * basisNorm Q)^12 *
          softFactor p n eps delta
            ((Real.sqrt ((2 : ℝ)^n) * basisNorm Q)^3 * B * s) ∧
        ∀ N : {F : (Matrix (Qubits n) (Qubits n) ℂ) →ₗ[ℂ] (Matrix (Qubits n) (Qubits n) ℂ) // IsChannel F},
          supportCount (fun ij : Fin (4 ^ n) × Fin (4 ^ n) => tm Q N ij.1 ij.2) ≤ s →
          let E := {r | ∀ rho O : (Matrix (Qubits n) (Qubits n) ℂ), IsDensityMatrix rho → O.IsHermitian →
            frobNorm O ≤ B * Real.sqrt ((2 : ℝ)^n) →
            |predict Q r rho O - (O * N.val rho).trace.re| ≤ eps}
          1 - delta ≤ choiReportEventProbability P N E := by sorry

end QAlgorithms.Papers.Independent.Extend50.P46

end
