-- Prove2me | Theorems.Thm_QMCProduct_HalfApprox_lemma_9
-- name    : QMCProduct.HalfApprox.lemma_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:49:00.076481+00:00
-- url     : https://prove2.me/theorems/5e6980ab-b7ae-44d9-904e-baafec0a4370
-- title:
--   Lemma 9, p. 28 — the level-k Lasserre value is a relaxation: νk(H) ≥ λmax(H)
-- statement:
--   Let $H$ be a Hermitian operator on $n$ qubits and $k\ge0$. Let $\widetilde\rho$ be an optimal solution of level $k$ of the quantum Lasserre hierarchy, i.e. a $k$-positive pseudo-density maximizing $\operatorname{Tr}(H\widetilde\rho)$, so that $\nu_k(H)=\operatorname{Tr}(H\widetilde\rho)$. Then for every density matrix $\sigma$ (positive semidefinite, trace one)
--   $$\operatorname{Tr}(H\sigma)\le\nu_k(H)=\operatorname{Tr}(H\widetilde\rho).$$
--   Since $\lambda_{\max}(H)=\max_\sigma\operatorname{Tr}(H\sigma)$, this is $\nu_k(H)\ge\lambda_{\max}(H)$: the hierarchy is a relaxation of the largest eigenvalue.
--
--   This is the inequality in equation (1) and the second inequality in the proof of Proposition 1.
--
--   **Formalization Note** $\lambda_{\max}(H)$ is expressed through comparison with every density matrix, and $\nu_k(H)$ through an optimal pseudo-density (equation (1) writes $\nu_k$ as a maximum). The paper proves the lemma in the equivalent vector-program form (Definition 17); the pseudo-density form is equation (1). Real parts of traces are taken; they are the full traces for Hermitian arguments.
-- source:
--   Parekh & Thompson, An Optimal Product-State Approximation for 2-Local Quantum Hamiltonians with Positive Terms, arXiv:2206.08342v2, p. 28, Lemma 9 (Appendix A.1); equation (1), p. 8

import Definitions.Def_QMCProduct_HalfApprox_Basic

set_option autoImplicit false

namespace QMCProduct.HalfApprox

/-- Lemma 9, p. 28: the level-k value `νk(H) = Tr[H ρt]` of an optimal k-positive
pseudo-density is at least `Tr[H σ]` for every density matrix `σ`, i.e. `νk(H) ≥ λmax(H)`. -/
theorem lemma_9 {n : ℕ} (k : ℕ) (H : Op n) (hH : H.IsHermitian)
    (ρt : Op n) (hopt : IsOptimalLk k H ρt) :
    ∀ σ : Op n, QAlgorithms.IsDensityMatrix σ →
      (H * σ).trace.re ≤ (H * ρt).trace.re := by sorry

end QMCProduct.HalfApprox
