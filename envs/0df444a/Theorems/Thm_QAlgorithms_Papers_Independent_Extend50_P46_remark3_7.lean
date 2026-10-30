-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P46_remark3_7
-- name    : QAlgorithms.Papers.Independent.Extend50.P46.remark3_7
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:17:35.589612+00:00
-- url     : https://prove2.me/theorems/41f5b4e8-86ef-44d9-b0dc-ff2ed64654b2
-- title:
--   Purity and rank restrictions on sparse states
-- statement:
--   Here $n\ge0$ is the number of qubits, $d=2^n$, states are positive semidefinite matrices of trace one, and $\mathcal N$ is a complex-linear CPTP map. The basis $Q=(Q_i)_{i=1}^{d^2}$ is a complete Hermitian Hilbert–Schmidt orthonormal basis. Write $R^Q_{ij}=\operatorname{tr}(Q_i\mathcal N(Q_j))$, $a_i=\operatorname{tr}(Q_i\rho)$ and $b_i=\operatorname{tr}(Q_iO)$. The norm $\|\cdot\|_2$ is the Hilbert–Schmidt norm, and $q=\max_i\|Q_i\|_\infty$ uses the spectral norm.
--
--   If $\rho$ is a density matrix with at most $s$ nonzero $Q$ coefficients, then
--
--   $$\operatorname{tr}(\rho^2)=\|\rho\|_2^2=\sum_i a_i^2\le sq^2,\qquad\operatorname{rank}(\rho)\ge\frac1{sq^2}.$$
--
--   In particular, for $q=2^{-n/2}$ and any specified polynomial sparsity envelope $s\le p(n)$, these give purity at most $p(n)/2^n$ and rank at least $2^n/p(n)$ on its positive regime. For any nonidentity Pauli $P_A$, both signs give states
--
--   $$\rho_\pm=2^{-n}(I\pm P_A),\qquad s_{\rho_\pm}=2,\qquad\|\rho_\pm-2^{-n}I\|_1=1.$$
--
--   Thus sparse states can remain far from maximally mixed in trace norm. The norm displayed here is not halved.
-- source:
--   Learning Quantum Processes and Hamiltonians via the Pauli Transfer Matrix, arXiv:2212.04471v2, PDF p. 18, Remark 3.7: purity and rank of sparse states

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P46

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P46

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.18, Remark 3.7: purity, rank, and the trace-norm distance example.
Exact bounds yield the stated polynomial-sparsity asymptotics uniformly for any
specified sparsity polynomial. Trace norm here is not divided by two. -/
theorem remark3_7 :
    (∀ {n : ℕ} (Q : HermitianBasis n) (rho : (Matrix (Qubits n) (Qubits n) ℂ)), IsDensityMatrix rho →
      ∀ s : ℕ, supportCount (coeff Q rho) ≤ s →
        (rho * rho).trace.re = frobNorm rho ^ 2 ∧
        (rho * rho).trace.re = ∑ i, coeff Q rho i ^ 2 ∧
        (rho * rho).trace.re ≤ (s : ℝ) * basisNorm Q ^ 2 ∧
        ((s : ℝ) * basisNorm Q ^ 2)⁻¹ ≤ (rho.rank : ℝ)) ∧
    (∀ {n : ℕ} (A : ErrorMitigation.PauliIndex n), A ≠ (fun _ => .I) → ∀ minus : Bool,
      IsDensityMatrix (eigenspaceState A minus) ∧
      supportCount (ErrorMitigation.pauliStateVector (eigenspaceState A minus)) = 2 ∧
      traceNorm (eigenspaceState A minus - (((2 : ℝ)^n)⁻¹ : ℂ) • (1 : (Matrix (Qubits n) (Qubits n) ℂ))) = 1) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P46

end
