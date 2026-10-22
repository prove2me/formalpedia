-- Prove2me | Theorems.Thm_WalledBrauer_Blocks_corollary_4_3
-- name    : WalledBrauer.Blocks.corollary_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:44:52.414301+00:00
-- url     : https://prove2.me/theorems/c6cb8cb1-bafa-4814-b59b-7c44c2797093
-- title:
--   Corollary 4.3 — the content condition for blocks
-- statement:
--   Let $k$ be an algebraically closed field of characteristic $0$ and $\delta\in k$. Let $(\lambda^L,\lambda^R)\in\Lambda^{r-a,s-a}$ and $(\mu^L,\mu^R)\in\Lambda^{r-b,s-b}$ be labels of simple $B_{r,s}(\delta)$-modules with $b-a=t\ge0$. If $L_{r,s}(\lambda^L,\lambda^R)$ and $L_{r,s}(\mu^L,\mu^R)$ are in the same block, then
--   $$
--   t\delta+\sum_{d\in[\lambda^L]}c(d)+\sum_{d\in[\lambda^R]}c(d)-\sum_{d\in[\mu^L]}c(d)-\sum_{d\in[\mu^R]}c(d)=0 .
--   $$
--
--   This is the first necessary condition for block membership. It gives the classification of blocks when $\delta\notin\mathbb Z$ (Theorem 4.4).
--
--   **Formalization Note** "Same block" means that no central idempotent of $B_{r,s}(\delta)$ separates the two simple modules (heads of the cell modules). The corollary is posed in characteristic $0$; the paper states it for every field.
-- source:
--   Cox, De Visscher, Doty & Martin, On the blocks of the walled Brauer algebra, arXiv:0709.0851v1, p. 19, Corollary 4.3

import Mathlib
import Definitions.Def_WalledBrauer_Blocks_CellModules
import Definitions.Def_WalledBrauer_Blocks_Partitions

namespace WalledBrauer.Blocks

/-- Corollary 4.3 (p. 19). Let `(λL, λR) ∈ Λ^{r-a,s-a}` and `(μL, μR) ∈ Λ^{r-b,s-b}` with
`b - a = t ≥ 0`. If `L_{r,s}(λL, λR)` and `L_{r,s}(μL, μR)` are in the same block then
`tδ + ∑_{[λL]} c + ∑_{[λR]} c - ∑_{[μL]} c - ∑_{[μR]} c = 0`. -/
theorem corollary_4_3 {k : Type*} [Field k] [CharZero k] [IsAlgClosed k] {r s : ℕ} {δ : k}
    (lam mu : Label r s δ) (hle : lam.t ≤ mu.t)
    (h : SameBlock (WalledBrauerAlgebra k r s δ) (SimpleModule lam) (SimpleModule mu)) :
    ((mu.t - lam.t : ℕ) : k) * δ + (totalContent lam.L : k) + (totalContent lam.R : k)
      - (totalContent mu.L : k) - (totalContent mu.R : k) = 0 := by sorry

end WalledBrauer.Blocks
