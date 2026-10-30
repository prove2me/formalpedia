-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P03_code_covariant
-- name    : QAlgorithms.Papers.Independent.Extend50.P03.code_covariant
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T12:51:26.180984+00:00
-- url     : https://prove2.me/theorems/e79a7305-e8c9-4be7-8d43-ae9bd499a2dc
-- title:
--   Proposition 1: covariance of every (n,k,α)-code
-- statement:
--   A code encodes $k$ logical qubits in $n$ physical qubits, with $0\le k\le n$, by appending a fixed normalized $(n-k)$-qubit eigenvector $\psi_\alpha$ of the Hamming-weight charge $Q^{(n-k)}$ with eigenvalue $0\le\alpha\le n-k$, then applying $U$. Thus $\mathcal E_U(\rho)=U(\rho\otimes|\psi_\alpha\rangle\langle\psi_\alpha|)U^\dagger$. The ancilla is chosen independently of $U$. The law $H_\times$ is probability Haar on the full charge centralizer, including every sector phase. Erasure of a set $S$ of $t\le n$ wires gives its complement to the decoder. Fidelity $F$ means root fidelity and $P=\sqrt{1-F^2}$. The optimized Choi error uses normalized $k$ EPR pairs; the optimized worst error chooses one CPTP decoder before all normalized joint logical/reference states over every finite reference dimension. For every charge-commuting unitary $U$, every real $\theta$, and every logical density matrix $\rho$,
--
--   $$\mathcal E_U(e^{i\theta Q^{(k)}}\rho e^{-i\theta Q^{(k)}})=e^{i\theta Q^{(n)}}\mathcal E_U(\rho)e^{-i\theta Q^{(n)}}.$$
--
--   This exact channel covariance holds for every sample of the random-code construction. The ancilla phase $e^{i\theta\alpha}$ cancels at the density-matrix level.
-- source:
--   Charge-conserving unitaries typically generate optimal covariant quantum error-correcting codes, arXiv:2102.11835v1, PDF p. 7, Proposition 1: covariance of every (n,k,α)-code

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P03

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Extend50.P03

open QAlgorithms.Papers.Independent.Support50.P23 (minEntropy)

attribute [local instance] Classical.propDecidable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P03.matrixContinuousENorm

/-- Proposition 1, PDF p.7: every constructed code is channel-covariant;
no false phase-free vector intertwining is required. -/
theorem code_covariant {n k alpha : ℕ} (A : Ancilla n k alpha)
    (U : (Matrix.unitaryGroup (Qubits n) ℂ)) (hU : Conserves U) : U1ChargeCovariant (chargeEncoder A U) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P03

end
