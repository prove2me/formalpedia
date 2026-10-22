-- Prove2me | Theorems.Thm_WalledBrauer_Blocks_theorem_4_2
-- name    : WalledBrauer.Blocks.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:45:00.648974+00:00
-- url     : https://prove2.me/theorems/b417cb8c-7580-4800-9ec7-7d1ba23fbf49
-- title:
--   Theorem 4.2 — the content condition for composition factors of cell modules
-- statement:
--   Let $k$ be an algebraically closed field of characteristic $0$ and $\delta\in k$. Let $(\lambda^L,\lambda^R)\in\Lambda^{r-a,s-a}$ be a label and $(\mu^L,\mu^R)\in\Lambda^{r-b,s-b}$. Suppose $[\Delta_{r,s}(\mu^L,\mu^R):L_{r,s}(\lambda^L,\lambda^R)]\ne 0$. Then $t=b-a\ge 0$ and
--   $$
--   t\delta+\sum_{d\in[\lambda^L]}c(d)+\sum_{d\in[\lambda^R]}c(d)-\sum_{d\in[\mu^L]}c(d)-\sum_{d\in[\mu^R]}c(d)=0 .
--   $$
--
--   The paper phrases the first part as "either $(\lambda^L,\lambda^R)=(\mu^L,\mu^R)$, or $b-a=t\ge0$". The equal case has $t=0$, and then the identity holds trivially, so the statement above is equivalent. The theorem gives a necessary condition for a nonzero decomposition number.
--
--   **Formalization Note** $[M:S]\ne0$ means $S\cong P/Q$ for submodules $Q\le P\le M$. $(\mu^L,\mu^R)$ ranges over all cell indices, including $(\emptyset,\emptyset)$ when $\delta=0$ and $r=s$. The theorem is posed in characteristic $0$; the paper states it for every field.
-- source:
--   Cox, De Visscher, Doty & Martin, On the blocks of the walled Brauer algebra, arXiv:0709.0851v1, p. 18, Theorem 4.2

import Mathlib
import Definitions.Def_WalledBrauer_Blocks_CellModules
import Definitions.Def_WalledBrauer_Blocks_Partitions

namespace WalledBrauer.Blocks

/-- Theorem 4.2 (p. 18). If `L_{r,s}(λL, λR)` (with `(λL, λR) ∈ Λ^{r-a,s-a}`) is a composition
factor of `Δ_{r,s}(μL, μR)` (with `(μL, μR) ∈ Λ^{r-b,s-b}`), then `t = b - a ≥ 0` and
`tδ + ∑_{[λL]} c + ∑_{[λR]} c - ∑_{[μL]} c - ∑_{[μR]} c = 0` (when `(λL, λR) = (μL, μR)`,
`t = 0` and the identity is trivial). -/
theorem theorem_4_2 {k : Type*} [Field k] [CharZero k] [IsAlgClosed k] {r s : ℕ} {δ : k}
    (lam : Label r s δ) (mu : CellIndex r s)
    (h : IsCompositionFactor (WalledBrauerAlgebra k r s δ) (SimpleModule lam) (CellModule δ mu)) :
    lam.t ≤ mu.t ∧
      ((mu.t - lam.t : ℕ) : k) * δ + (totalContent lam.L : k) + (totalContent lam.R : k)
        - (totalContent mu.L : k) - (totalContent mu.R : k) = 0 := by sorry

end WalledBrauer.Blocks
