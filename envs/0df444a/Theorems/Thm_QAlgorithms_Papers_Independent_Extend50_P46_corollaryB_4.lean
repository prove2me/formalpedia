-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P46_corollaryB_4
-- name    : QAlgorithms.Papers.Independent.Extend50.P46.corollaryB_4
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:11:18.793835+00:00
-- url     : https://prove2.me/theorems/a0918ac7-d778-4a63-83e2-6b2e08252d2c
-- title:
--   Uniform sparse prediction in a general Hermitian operator basis
-- statement:
--   The unknown channel is an arbitrary complex-linear CPTP map on $n$ qubits. Choi access supplies independent copies of the normalized reference-first state $J(\mathcal N)=(\mathrm{id}\otimes\mathcal N)(|\Omega\rangle\langle\Omega|)$. The algorithm is a joint POVM on exactly its stated number of copies, chosen before the channel. Accuracy means simultaneous absolute error under its actual Born law. All constants, and all exponents hidden in $\widetilde O$, are uniform before the channel, dimension, basis and accuracy parameters. Assume $\varepsilon>0$ and $0<\delta<1$.
--
--   Here $n\ge0$ is the number of qubits, $d=2^n$, states are positive semidefinite matrices of trace one, and $\mathcal N$ is a complex-linear CPTP map. The basis $Q=(Q_i)_{i=1}^{d^2}$ is a complete Hermitian Hilbert–Schmidt orthonormal basis. Write $R^Q_{ij}=\operatorname{tr}(Q_i\mathcal N(Q_j))$, $a_i=\operatorname{tr}(Q_i\rho)$ and $b_i=\operatorname{tr}(Q_iO)$. The norm $\|\cdot\|_2$ is the Hilbert–Schmidt norm, and $q=\max_i\|Q_i\|_\infty$ uses the spectral norm.
--
--   Fix natural-number sparsity envelopes $s_\rho,s_O$ and $B>0$. A learner uses
--
--   $$m=\widetilde O\!\left(\frac{n^3+n\log(1/\delta)}{\varepsilon^4}B^4s_\rho^4s_O^2(\sqrt{2^n}q)^{12}\right)$$
--
--   copies and produces a classical table. With probability at least $1-\delta$, its explicit coefficient contraction predicts every expectation $\operatorname{tr}(O\mathcal N(\rho))$ within $\varepsilon$, simultaneously over states with at most $s_\rho$ nonzero $Q$ coefficients and Hermitian observables with at most $s_O$ nonzero $Q$ coefficients and $\|O\|_2\le B\sqrt{2^n}$.
--
--   This extends the uniform sparse-prediction guarantee beyond the Pauli basis.
-- source:
--   Learning Quantum Processes and Hamiltonians via the Pauli Transfer Matrix, arXiv:2212.04471v2, PDF p. 40, Corollary B.4

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P46

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P46

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.40-41, Corollary B.4. One classical table predicts simultaneously
for every promised sparse state and observable; the norm factor has exponent twelve. -/
theorem corollaryB_4 :
    ∃ C : ℝ, 0 < C ∧ ∃ p : ℕ, ∀ n srho sO : ℕ,
      ∀ Q : HermitianBasis n, ∀ B eps delta : ℝ,
      0 < B → 0 < eps → 0 < delta → delta < 1 →
      ∃ P : ChoiLearner n (Matrix (Fin (4 ^ n)) (Fin (4 ^ n)) ℝ),
        (P.copies : ℝ) ≤ C * ((n : ℝ)^3 + n * Real.log delta⁻¹) / eps^4 *
          B^4 * (srho : ℝ)^4 * (sO : ℝ)^2 *
          (Real.sqrt ((2 : ℝ)^n) * basisNorm Q)^12 *
          softFactor p n eps delta
            ((Real.sqrt ((2 : ℝ)^n) * basisNorm Q)^3 * B * srho * Real.sqrt sO) ∧
        ∀ N : {F : (Matrix (Qubits n) (Qubits n) ℂ) →ₗ[ℂ] (Matrix (Qubits n) (Qubits n) ℂ) // IsChannel F},
          let E := {r | ∀ rho O : (Matrix (Qubits n) (Qubits n) ℂ), IsDensityMatrix rho → O.IsHermitian →
            supportCount (coeff Q rho) ≤ srho → supportCount (coeff Q O) ≤ sO →
            frobNorm O ≤ B * Real.sqrt ((2 : ℝ)^n) →
            |predict Q r rho O - (O * N.val rho).trace.re| ≤ eps}
          1 - delta ≤ choiReportEventProbability P N E := by sorry

end QAlgorithms.Papers.Independent.Extend50.P46

end
