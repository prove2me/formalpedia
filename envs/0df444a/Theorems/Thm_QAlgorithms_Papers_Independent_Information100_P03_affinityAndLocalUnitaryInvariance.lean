-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P03_affinityAndLocalUnitaryInvariance
-- name    : QAlgorithms.Papers.Independent.Information100.P03.affinityAndLocalUnitaryInvariance
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:27:29.827849+00:00
-- url     : https://prove2.me/theorems/02ff3b56-861d-41e3-a731-13a4b98081e4
-- title:
--   Affinity and local-unitary trace-norm invariance
-- statement:
--   Let $d_A,d_B\ge1$ be finite local dimensions and let $P\in\mathbb R^{m\times r}$, $Q\in\mathbb R^{n\times r}$, $\mu,\nu\in\mathbb R^r$ satisfy $\nu^T\mu=1$. The auxiliary row counts $m,n$ are independent of the local dimensions; no rank assumption is imposed. For a bipartite density matrix $\rho$ (positive semidefinite with trace one), write $\rho_A=\operatorname{Tr}_B\rho$ and $\rho_B=\operatorname{Tr}_A\rho$. Column vectorization stacks columns, and realignment satisfies $R(X\otimes Y)=\operatorname{vec}(X)\operatorname{vec}(Y)^T$, with an ordinary transpose. Define
--
--   $$
--   \mathcal Q(\rho)=\begin{pmatrix}PQ^T&P\mu\operatorname{vec}(\rho_B)^T\\operatorname{vec}(\rho_A)\nu^TQ^T&R(\rho)\end{pmatrix},\qquad
--   M=\left\|(P^TP+\nu\nu^T)^{1/2}(Q^TQ+\mu\mu^T)^{1/2}\right\|_{\rm tr}.
--   $$
--
--   Here the square roots are the positive semidefinite square roots and $\|\cdot\|_{\rm tr}$ denotes the sum of singular values, including for rectangular matrices.
--
--   For any finite family of density matrices $\rho_k$ and real weights $p_k\ge0$ with $\sum_kp_k=1$, and any local unitaries $U\in U(d_A)$, $V\in U(d_B)$,
--
--   $$\mathcal Q\!\left(\sum_kp_k\rho_k\right)=\sum_kp_k\mathcal Q(\rho_k),\qquad
--   \|\mathcal Q((U\otimes V)\rho(U\otimes V)^\dagger)\|_{\rm tr}=\|\mathcal Q(\rho)\|_{\rm tr}.$$
--
--   These are affinity on normalized mixtures and invariance under changes of local orthonormal bases.
-- source:
--   Separability criteria and lower bounds of entanglement via realignment, arXiv:2610.15664v1, PDF p. 3, Lemma 1; Appendix A pp.12–14

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P03

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Information100.P03

/-- PDF p.3, Lemma 1 (both clauses), Appendix A pp.12--14: affinity on
normalized convex mixtures, and local-unitary invariance of the trace norm. -/
theorem affinityAndLocalUnitaryInvariance {dA dB m n r : ℕ} [NeZero dA] [NeZero dB]
    (z : Parameters m n r) :
    (∀ (K : ℕ) (p : Fin K → ℝ)
      (rho : Fin K → Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ),
      (∀ k, 0 ≤ p k) → (∑ k, p k) = 1 → (∀ k, IsDensityMatrix (rho k)) →
      enhanced z (∑ k, (p k : ℂ) • rho k) =
        ∑ k, (p k : ℂ) • enhanced z (rho k)) ∧
    (∀ (rho : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ),
      IsDensityMatrix rho → ∀ (U : Matrix.unitaryGroup (Fin dA) ℂ)
      (V : Matrix.unitaryGroup (Fin dB) ℂ),
      nuclearNorm (enhanced z
        (Matrix.kronecker (U : Matrix (Fin dA) (Fin dA) ℂ) (V : Matrix (Fin dB) (Fin dB) ℂ) *
          rho * (Matrix.kronecker (U : Matrix (Fin dA) (Fin dA) ℂ)
            (V : Matrix (Fin dB) (Fin dB) ℂ))ᴴ)) = nuclearNorm (enhanced z rho)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P03

end
