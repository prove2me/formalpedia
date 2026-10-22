-- Prove2me | Theorems.Thm_QMCProduct_HalfApprox_proposition_1
-- name    : QMCProduct.HalfApprox.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:49:14.102175+00:00
-- url     : https://prove2.me/theorems/42317914-9bf9-42e2-b211-95505e7fe18e
-- title:
--   Proposition 1, p. 9 — for a strictly quadratic 2-local H, edgewise Tr[Hij ρ] ≥ α µij gives an α-approximation of λmax(H)
-- statement:
--   Let $H=\sum_{ij\in E}w_{ij}H_{ij}$ be a strictly quadratic 2-local Hamiltonian (Definition 3): each edge $ij$ of a graph on $n$ qubits is counted once, carries a weight $w_{ij}\ge0$, and has a local term
--   $$H_{ij}=c_{ij}(I)\,I+\sum_{\tau,\sigma\in\{X,Y,Z\}}c_{ij}(\tau\sigma)\,\tau_i\sigma_j\succeq0,\qquad c_{ij}(\cdot)\in\mathbb R.$$
--   Let $\widetilde\rho$ be an optimal level-$k$ Lasserre solution for $H$ and, with $\langle\phi\rangle=\operatorname{Tr}(\widetilde\rho\phi)$, let $\mu_{ij}=c_{ij}(I)+\sum_{\tau,\sigma}c_{ij}(\tau\sigma)\langle\tau_i\sigma_j\rangle$ be the relaxed edge energies of Definition 7. Let $\rho$ be a density matrix and $\alpha\in(0,1]$. If for each edge $ij\in E$
--   $$\operatorname{Tr}(H_{ij}\rho)\ge\alpha\,\mu_{ij},$$
--   then $\rho$ is an $\alpha$-approximation of $\lambda_{\max}(H)$:
--   $$\operatorname{Tr}(H\rho)\ge\alpha\,\operatorname{Tr}(H\sigma)\quad\text{for every density matrix }\sigma,\qquad\text{i.e.}\quad\operatorname{Tr}(H\rho)\ge\alpha\lambda_{\max}(H).$$
--
--   This reduces the global approximation guarantee to an edge-by-edge comparison with the relaxed energies, and is how Theorem 3 is assembled from equation (12), Fact 1 and the $\delta(L)$ bound. Quantum Max Cut is the case $c_{ij}(I)=1/4$, $c_{ij}(\tau\tau)=-1/4$ and $c_{ij}(\tau\sigma)=0$ for $\tau\ne\sigma$, where $\mu_{ij}$ is Definition 12's.
--
--   **Formalization Note** The local term of Definition 3 is `sqTerm`, with $X,Y,Z$ coded by `0, 1, 2 : Fin 3`. The level $k$ is arbitrary, as on the page. $\lambda_{\max}(H)$ is expressed by comparison with every density matrix. The weights are taken nonnegative, as in §3.2.2; Definition 3 assumes them positive, and an edge of weight zero only adds a hypothesis, so the two versions have the same content. Traces of Hermitian expressions are compared through their real parts.
-- source:
--   Parekh & Thompson, An Optimal Product-State Approximation for 2-Local Quantum Hamiltonians with Positive Terms, arXiv:2206.08342v2, p. 9, Proposition 1 (with Definitions 3 and 7, pp. 7–8)

import Definitions.Def_QMCProduct_HalfApprox_Basic

set_option autoImplicit false

namespace QMCProduct.HalfApprox

open scoped ComplexOrder

/-- Proposition 1, p. 9, for a strictly quadratic 2-local Hamiltonian (Definition 3, p. 7)
`H = ∑_{ij ∈ E} w_ij H_ij` with `H_ij ⪰ 0`: if edgewise `Tr[H_ij ρ] ≥ α µ_ij`, where `µ_ij` is
Definition 7's relaxed value from an optimal level-k pseudo-density, then `Tr[H ρ] ≥ α Tr[H σ]`
for every density matrix `σ`, i.e. `Tr[H ρ] ≥ α λmax(H)`. -/
theorem proposition_1 {n : ℕ} (k : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Fin n → Fin n → ℝ) (hw : ∀ e ∈ edges G, 0 ≤ w e.1 e.2)
    (c0 : Fin n → Fin n → ℝ) (c : Fin n → Fin n → Fin 3 → Fin 3 → ℝ)
    (hpsd : ∀ e ∈ edges G, (sqTerm (c0 e.1 e.2) (c e.1 e.2) e.1 e.2).PosSemidef)
    (ρt : Op n)
    (hopt : IsOptimalLk k
      (∑ e ∈ edges G, (w e.1 e.2 : ℂ) • sqTerm (c0 e.1 e.2) (c e.1 e.2) e.1 e.2) ρt)
    (ρ : Op n) (hρ : QAlgorithms.IsDensityMatrix ρ)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hedge : ∀ e ∈ edges G,
      α * (c0 e.1 e.2 + ∑ a : Fin 3, ∑ b : Fin 3, c e.1 e.2 a b *
          val ρt (onSite e.1 (pauli1 a.succ) * onSite e.2 (pauli1 b.succ))) ≤
        (sqTerm (c0 e.1 e.2) (c e.1 e.2) e.1 e.2 * ρ).trace.re) :
    ∀ σ : Op n, QAlgorithms.IsDensityMatrix σ →
      α * ((∑ e ∈ edges G, (w e.1 e.2 : ℂ) • sqTerm (c0 e.1 e.2) (c e.1 e.2) e.1 e.2) *
          σ).trace.re ≤
        ((∑ e ∈ edges G, (w e.1 e.2 : ℂ) • sqTerm (c0 e.1 e.2) (c e.1 e.2) e.1 e.2) *
          ρ).trace.re := by sorry

end QMCProduct.HalfApprox
