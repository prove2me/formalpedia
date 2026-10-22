-- Prove2me | Theorems.Thm_WalledBrauer_Blocks_corollary_8_4
-- name    : WalledBrauer.Blocks.corollary_8_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:45:04.552558+00:00
-- url     : https://prove2.me/theorems/870d3fe2-1d4d-413d-bba4-f9d9947d3acf
-- title:
--   Corollary 8.4 (characteristic $0$) — blocks of $B_{r,s}(\delta)$ are orbits of the $\rho(\delta)$-shifted dot action of $\Sigma_{r+s}$
-- statement:
--   Let $k$ be an algebraically closed field of characteristic $0$, let $r,s\in\mathbb N$ and $\delta\in\mathbb Z$, and let $B_{r,s}(\delta)$ be the walled Brauer algebra over $k$. Let $\lambda=(\lambda^L,\lambda^R)$ and $\mu=(\mu^L,\mu^R)$ be labels of simple $B_{r,s}(\delta)$-modules. These are bipartitions $\lambda^L\vdash r-a$, $\lambda^R\vdash s-a$ with $0\le a\le\min(r,s)$, excluding $(\emptyset,\emptyset)$ when $\delta=0$ and $r=s$. Then $L_{r,s}(\lambda)$ and $L_{r,s}(\mu)$ lie in the same block if and only if
--   $$
--   (\bar\lambda^L;\lambda^R)=w.(\bar\mu^L;\mu^R)\quad\text{for some } w\in W=\Sigma_{r+s},
--   $$
--   where $w.v=w(v+\rho)-\rho$ with $\rho=\rho(\delta)=(r,r-1,\dots,1;\ \delta,\delta-1,\dots,\delta-s+1)$, and $(\bar\lambda^L;\lambda^R)=(-\lambda^L_r,\dots,-\lambda^L_1;\lambda^R_1,\dots,\lambda^R_s)$ is the embedding (23) of a bipartition into the weight lattice $X_{r,s}$.
--
--   This is the paper's description of the blocks in characteristic zero by an alcove-type geometry for $\Sigma_{r+s}$. In positive characteristic, Section 10 turns it into a linkage principle.
--
--   **Formalization Note** The paper's hypothesis "$k$ is $\Sigma$-semisimple with $\delta\in\mathbb Z$" also allows characteristic $p>\max(r,s)$; this statement takes characteristic $0$. $\delta$ is an integer cast into $k$. The algebra is the walled Brauer algebra with the $\delta^{\#\text{loops}}$ product, not the centraliser algebra on mixed tensor space. $L_{r,s}(\lambda)$ is the head of the cell module, and "same block" means that no central idempotent separates the two simple modules. The weight lattice is `Fin r ⊕ Fin s → ℤ`, with `Sum.inl i` the paper's coordinate $-(i+1)$ and `Sum.inr j` coordinate $j+1$.
-- source:
--   Cox, De Visscher, Doty & Martin, On the blocks of the walled Brauer algebra, arXiv:0709.0851v1, p. 36, Corollary 8.4

import Mathlib
import Definitions.Def_WalledBrauer_Blocks_CellModules
import Definitions.Def_WalledBrauer_Blocks_Weights

namespace WalledBrauer.Blocks

/-- Corollary 8.4 (p. 36), in characteristic zero. Let `k` be an algebraically closed field of
characteristic zero, `r, s ∈ ℕ` and `δ ∈ ℤ`. Two labels `λ = (λL, λR)` and `μ = (μL, μR)` of
simple `B_{r,s}(δ)`-modules lie in the same block (no central idempotent separates
`L_{r,s}(λ)` and `L_{r,s}(μ)`) if and only if `(λ̄L; λR) = w.(μ̄L; μR)` for some `w ∈ W = Σ_{r+s}`,
where `w.v = w(v + ρ(δ)) - ρ(δ)` and `ρ(δ) = (r, …, 1; δ, …, δ - s + 1)`. -/
theorem corollary_8_4 {k : Type*} [Field k] [CharZero k] [IsAlgClosed k] (r s : ℕ) (δ : ℤ)
    (lam mu : Label r s (δ : k)) :
    SameBlock (WalledBrauerAlgebra k r s (δ : k)) (SimpleModule lam) (SimpleModule mu) ↔
      ∃ w : Equiv.Perm (Fin r ⊕ Fin s),
        weight r s lam.L lam.R = dotAct r s δ w (weight r s mu.L mu.R) := by sorry

end WalledBrauer.Blocks
