-- Prove2me | Theorems.Thm_WalledBrauer_Blocks_proposition_7_1
-- name    : WalledBrauer.Blocks.proposition_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:44:53.195326+00:00
-- url     : https://prove2.me/theorems/4ca93765-04c5-4b28-aec2-eb3b3c165104
-- title:
--   Proposition 7.1 — composition factors of cell modules: containment and a $-\delta$ pairing
-- statement:
--   Let $k$ be an algebraically closed field of characteristic $0$ and $\delta\in k$. Let $(\lambda^L,\lambda^R)$ be a label and $(\mu^L,\mu^R)$ a cell index. Suppose $[\Delta_{r,s}(\mu^L,\mu^R):L_{r,s}(\lambda^L,\lambda^R)]\ne0$. Then $(\mu^L,\mu^R)\subseteq(\lambda^L,\lambda^R)$, i.e. $\mu^L\subseteq\lambda^L$ and $\mu^R\subseteq\lambda^R$. Moreover, there is a pairing of the boxes of $\lambda^L/\mu^L$ with those of $\lambda^R/\mu^R$ such that
--   $$
--   c(d)+c(d')=-\delta\quad\text{for every pair } (d,d').
--   $$
--
--   This refines Theorem 4.2 from a condition on total contents to a box-by-box condition. It leads to the notion of balanced bipartitions.
--
--   **Formalization Note** $[M:S]\ne0$ means $S\cong P/Q$ for submodules $Q\le P\le M$. The pairing is a bijection between the cell-set differences with contents summing to $-\delta$ in $k$.
-- source:
--   Cox, De Visscher, Doty & Martin, On the blocks of the walled Brauer algebra, arXiv:0709.0851v1, p. 26, Proposition 7.1

import Mathlib
import Definitions.Def_WalledBrauer_Blocks_CellModules
import Definitions.Def_WalledBrauer_Blocks_Partitions

namespace WalledBrauer.Blocks

/-- Proposition 7.1 (p. 26). In characteristic zero, if `L_{r,s}(λL, λR)` is a composition
factor of `Δ_{r,s}(μL, μR)` then `(μL, μR) ⊆ (λL, λR)`, and the boxes of `λL/μL` can be paired
with those of `λR/μR` so that the contents of each pair sum to `-δ`. -/
theorem proposition_7_1 {k : Type*} [Field k] [CharZero k] [IsAlgClosed k] {r s : ℕ} {δ : k}
    (lam : Label r s δ) (mu : CellIndex r s)
    (h : IsCompositionFactor (WalledBrauerAlgebra k r s δ) (SimpleModule lam) (CellModule δ mu)) :
    mu.L ≤ lam.L ∧ mu.R ≤ lam.R ∧
      PairsToNegDelta δ (lam.L.cells \ mu.L.cells) (lam.R.cells \ mu.R.cells) := by sorry

end WalledBrauer.Blocks
