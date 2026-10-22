-- Prove2me | Theorems.Thm_WalledBrauer_Blocks_corollary_7_7
-- name    : WalledBrauer.Blocks.corollary_7_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:45:05.571011+00:00
-- url     : https://prove2.me/theorems/22a7cedf-41b5-4452-bd5f-ecab0ecc4aba
-- title:
--   Corollary 7.7 — blocks are the balanced classes, each with a unique minimal weight
-- statement:
--   Let $k$ be an algebraically closed field of characteristic $0$ and $\delta\in k$.
--
--   1. Two labels $(\lambda^L,\lambda^R)$ and $(\mu^L,\mu^R)$ are in the same block of $B_{r,s}(\delta)$ if and only if they are $\delta$-balanced.
--   2. Each block contains a unique minimal weight. That is, for every label $\lambda$ there is exactly one label $\mu$ in the block of $\lambda$ such that no other label of that block is contained in $\mu$ componentwise.
--
--   This is the block classification of the walled Brauer algebra in characteristic zero.
--
--   **Formalization Note** Containment is componentwise inclusion of Young diagrams ($\nu^L\subseteq\mu^L$ and $\nu^R\subseteq\mu^R$). "Minimal" is the condition $\nu\subseteq\mu$, $\nu$ in the block $\Rightarrow\nu=\mu$. Labels exclude $(\emptyset,\emptyset)$ when $\delta=0$ and $r=s$. The result holds for every $\delta\in k$, integral or not.
-- source:
--   Cox, De Visscher, Doty & Martin, On the blocks of the walled Brauer algebra, arXiv:0709.0851v1, p. 30, Corollary 7.7

import Mathlib
import Definitions.Def_WalledBrauer_Blocks_CellModules
import Definitions.Def_WalledBrauer_Blocks_Partitions

namespace WalledBrauer.Blocks

/-- Corollary 7.7 (p. 30). In characteristic zero, two weights `(λL, λR)` and `(μL, μR)` are in
the same block of `B_{r,s}(δ)` if and only if they are balanced. Each block contains a unique
minimal weight (minimal for componentwise containment of Young diagrams). -/
theorem corollary_7_7 {k : Type*} [Field k] [CharZero k] [IsAlgClosed k] {r s : ℕ} (δ : k) :
    (∀ lam mu : Label r s δ,
      SameBlock (WalledBrauerAlgebra k r s δ) (SimpleModule lam) (SimpleModule mu) ↔
        IsBalanced δ lam.L lam.R mu.L mu.R) ∧
    (∀ lam : Label r s δ, ∃! mu : Label r s δ,
      SameBlock (WalledBrauerAlgebra k r s δ) (SimpleModule lam) (SimpleModule mu) ∧
      ∀ nu : Label r s δ,
        SameBlock (WalledBrauerAlgebra k r s δ) (SimpleModule lam) (SimpleModule nu) →
          nu.L ≤ mu.L → nu.R ≤ mu.R → nu = mu) := by sorry

end WalledBrauer.Blocks
