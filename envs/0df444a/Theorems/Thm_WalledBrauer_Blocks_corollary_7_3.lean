-- Prove2me | Theorems.Thm_WalledBrauer_Blocks_corollary_7_3
-- name    : WalledBrauer.Blocks.corollary_7_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:45:00.293468+00:00
-- url     : https://prove2.me/theorems/b8d20058-cec7-4303-a9be-c187d03df97f
-- title:
--   Corollary 7.3 — weights in the same block are $\delta$-balanced
-- statement:
--   Let $k$ be an algebraically closed field of characteristic $0$ and $\delta\in k$. If the labels $(\lambda^L,\lambda^R)$ and $(\mu^L,\mu^R)$ are in the same block for $B_{r,s}(\delta)$, then they are $\delta$-balanced (Definition 7.2).
--
--   This is the necessity half of the block classification in characteristic zero.
--
--   **Formalization Note** "In the same block" refers to the simple modules $L_{r,s}(\lambda^L,\lambda^R)$ and $L_{r,s}(\mu^L,\mu^R)$: no central idempotent of $B_{r,s}(\delta)$ separates them. Balance is taken in $k$.
-- source:
--   Cox, De Visscher, Doty & Martin, On the blocks of the walled Brauer algebra, arXiv:0709.0851v1, p. 28, Corollary 7.3

import Mathlib
import Definitions.Def_WalledBrauer_Blocks_CellModules
import Definitions.Def_WalledBrauer_Blocks_Partitions

namespace WalledBrauer.Blocks

/-- Corollary 7.3 (p. 28). In characteristic zero, if `(λL, λR)` and `(μL, μR)` are in the same
block for `B_{r,s}(δ)` then they are `δ`-balanced. -/
theorem corollary_7_3 {k : Type*} [Field k] [CharZero k] [IsAlgClosed k] {r s : ℕ} {δ : k}
    (lam mu : Label r s δ)
    (h : SameBlock (WalledBrauerAlgebra k r s δ) (SimpleModule lam) (SimpleModule mu)) :
    IsBalanced δ lam.L lam.R mu.L mu.R := by sorry

end WalledBrauer.Blocks
