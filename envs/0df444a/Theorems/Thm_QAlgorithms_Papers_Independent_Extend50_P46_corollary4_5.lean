-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P46_corollary4_5
-- name    : QAlgorithms.Papers.Independent.Extend50.P46.corollary4_5
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:08:27.262348+00:00
-- url     : https://prove2.me/theorems/057a2509-88e1-4154-aa16-abfd1c2ca2f5
-- title:
--   Prediction of arbitrary bounded observables for sparse channels
-- statement:
--   The unknown channel is an arbitrary complex-linear CPTP map on $n$ qubits. Choi access supplies independent copies of the normalized reference-first state $J(\mathcal N)=(\mathrm{id}\otimes\mathcal N)(|\Omega\rangle\langle\Omega|)$. The algorithm is a joint POVM on exactly its stated number of copies, chosen before the channel. Accuracy means simultaneous absolute error under its actual Born law. All constants, and all exponents hidden in $\widetilde O$, are uniform before the channel, dimension, basis and accuracy parameters. Assume $\varepsilon>0$ and $0<\delta<1$.
--
--   Let $s\ge1$ and $B>0$ be known bounds. If the PTM has at most $s$ nonzero entries, there is a learner using
--
--   $$m=O\!\left(\frac{n+\log(1/\delta)}{\varepsilon^4}B^4s^4\right)$$
--
--   copies whose classical table predicts, on one common event of probability at least $1-\delta$, every $\operatorname{tr}(O\mathcal N(\rho))$ within $\varepsilon$ for every state $\rho$ and Hermitian $O$ satisfying $\|O\|_2\le B\sqrt{2^n}$. Neither state nor observable sparsity is required. The predictor is the explicit contraction of the learned PTM with their Pauli coefficient vectors.
--
--   This gives a uniform prediction guarantee without assuming the support of the channel is known.
-- source:
--   Learning Quantum Processes and Hamiltonians via the Pauli Transfer Matrix, arXiv:2212.04471v2, PDF p. 24, Corollary 4.5

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P46

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P46

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.24, Corollary 4.5: one classical table predicts all bounded
observables on all states; neither input sparsity nor known channel support is assumed. -/
theorem corollary4_5 :
    ∃ C : ℝ, 0 < C ∧ ∀ n s : ℕ, 1 ≤ s → ∀ B eps delta : ℝ,
      0 < B → 0 < eps → 0 < delta → delta < 1 →
      ∃ P : ChoiLearner n (Matrix (ErrorMitigation.PauliIndex n) (ErrorMitigation.PauliIndex n) ℝ),
        (P.copies : ℝ) ≤ C * (n + Real.log delta⁻¹) / eps^4 * B^4 * (s : ℝ)^4 ∧
        ∀ N : {F : (Matrix (Qubits n) (Qubits n) ℂ) →ₗ[ℂ] (Matrix (Qubits n) (Qubits n) ℂ) // IsChannel F}, supportCount (fun p : ErrorMitigation.PauliIndex n × ErrorMitigation.PauliIndex n => ptm N p.1 p.2) ≤ s →
          let E := {r | ∀ rho O : (Matrix (Qubits n) (Qubits n) ℂ), IsDensityMatrix rho → O.IsHermitian →
            frobNorm O ≤ B * Real.sqrt ((2 : ℝ)^n) →
            |predictPauli r rho O - (O * N.val rho).trace.re| ≤ eps}
          1 - delta ≤ choiReportEventProbability P N E := by sorry

end QAlgorithms.Papers.Independent.Extend50.P46

end
