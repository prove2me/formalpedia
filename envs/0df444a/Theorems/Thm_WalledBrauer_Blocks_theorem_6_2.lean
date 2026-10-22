-- Prove2me | Theorems.Thm_WalledBrauer_Blocks_theorem_6_2
-- name    : WalledBrauer.Blocks.theorem_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:44:55.891241+00:00
-- url     : https://prove2.me/theorems/a34f9594-18b4-4b4f-bf78-17daaf4c3022
-- title:
--   Theorem 6.2 — two-box homomorphisms: $\mathrm{Hom}(\Delta(\lambda),\Delta(\mu))\cong k$
-- statement:
--   Let $k$ be an algebraically closed field of characteristic $0$ and $\delta\in k$. Let $(\lambda^L,\lambda^R)\in\Lambda^{r-t,s-t}$ and $(\mu^L,\mu^R)\in\Lambda^{r-t-1,s-t-1}$. Suppose $(\mu^L,\mu^R)\lhd(\lambda^L,\lambda^R)$, i.e. $(\mu^L,\mu^R)$ is obtained by removing one box from $\lambda^L$ and one from $\lambda^R$. Suppose further that
--   $$
--   c(\lambda^L/\mu^L)+c(\lambda^R/\mu^R)+\delta=0 ,
--   $$
--   where $c(\lambda/\mu)$ is the content of the unique box of $[\lambda/\mu]$. Then
--   $$
--   \operatorname{Hom}_{B_{r,s}}\big(\Delta_{r,s}(\lambda^L,\lambda^R),\Delta_{r,s}(\mu^L,\mu^R)\big)\cong k .
--   $$
--
--   These two-box homomorphisms are the basic links between cell modules, from which the block classification in characteristic zero is assembled.
--
--   **Formalization Note** $\operatorname{Hom}\cong k$ is stated as `Module.finrank k (Δλ →ₗ[B] Δμ) = 1`. Since the sizes of the diagrams are fixed by the indices, $(\mu^L,\mu^R)\lhd(\lambda^L,\lambda^R)$ is encoded as $\mu^L\subseteq\lambda^L$ and $\mu^R\subseteq\lambda^R$. Then each skew diagram has one box, and $c(\lambda/\mu)$ is the sum of contents over the cell-set difference.
-- source:
--   Cox, De Visscher, Doty & Martin, On the blocks of the walled Brauer algebra, arXiv:0709.0851v1, p. 21, Theorem 6.2

import Mathlib
import Definitions.Def_WalledBrauer_Blocks_CellModules
import Definitions.Def_WalledBrauer_Blocks_Partitions

namespace WalledBrauer.Blocks

/-- Theorem 6.2 (p. 21). Let `(λL, λR) ∈ Λ^{r-t,s-t}` and `(μL, μR) ∈ Λ^{r-t-1,s-t-1}` with
`(μL, μR) ◁ (λL, λR)` (obtained by removing one box from `λL` and one from `λR`). If
`c(λL/μL) + c(λR/μR) + δ = 0` then `Hom_{B_{r,s}}(Δ_{r,s}(λL, λR), Δ_{r,s}(μL, μR)) ≅ k`. -/
theorem theorem_6_2 {k : Type*} [Field k] [CharZero k] [IsAlgClosed k] {r s : ℕ} (δ : k)
    (lam mu : CellIndex r s) (ht : mu.t = lam.t + 1)
    (hL : mu.L ≤ lam.L) (hR : mu.R ≤ lam.R)
    (hc : (∑ d ∈ lam.L.cells \ mu.L.cells, (content d : k)) +
      (∑ d ∈ lam.R.cells \ mu.R.cells, (content d : k)) + δ = 0) :
    Module.finrank k (CellModule δ lam →ₗ[WalledBrauerAlgebra k r s δ] CellModule δ mu) = 1 := by sorry

end WalledBrauer.Blocks
