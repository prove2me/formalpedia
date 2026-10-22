-- Prove2me | Theorems.Thm_WalledBrauer_Blocks_proposition_8_2
-- name    : WalledBrauer.Blocks.proposition_8_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:43:19.099306+00:00
-- url     : https://prove2.me/theorems/a91b9e47-e2da-4123-b917-ac55d5489173
-- title:
--   Proposition 8.2 — bipartitions in one dot orbit are $\delta$-balanced
-- statement:
--   Let $r,s\in\mathbb N$ and $\delta\in\mathbb Z$. Let $(\lambda^L,\lambda^R)$ and $(\mu^L,\mu^R)$ be bipartitions with at most $r$ and $s$ rows respectively. Suppose that for some $w\in W=\Sigma_{r+s}$
--   $$
--   (\bar\mu^L;\mu^R)=w.(\bar\lambda^L;\lambda^R),
--   $$
--   where $w.v=w(v+\rho(\delta))-\rho(\delta)$ and $(\bar\lambda^L;\lambda^R)$ is the embedding (23). Then $(\lambda^L,\lambda^R)$ and $(\mu^L,\mu^R)$ are $\delta$-balanced.
--
--   This is the first half of the translation of balance into Weyl-group geometry.
--
--   **Formalization Note** "At most $r$ rows" is `λ.colLen 0 ≤ r`. Without the row bounds, the embedding (23) would silently drop rows. The sizes of the bipartitions are not constrained. Balance is taken in $\mathbb Z$.
-- source:
--   Cox, De Visscher, Doty & Martin, On the blocks of the walled Brauer algebra, arXiv:0709.0851v1, p. 33, Proposition 8.2

import Mathlib
import Definitions.Def_WalledBrauer_Blocks_Partitions
import Definitions.Def_WalledBrauer_Blocks_Weights

namespace WalledBrauer.Blocks

/-- Proposition 8.2 (p. 33). Let `δ ∈ ℤ` and let `(λL, λR)`, `(μL, μR)` be bipartitions with at
most `r` and `s` rows. If `(μ̄L; μR) = w.(λ̄L; λR)` for some `w ∈ W = Σ_{r+s}` (dot action with
respect to `ρ(δ)`), then `(λL, λR)` and `(μL, μR)` are `δ`-balanced. -/
theorem proposition_8_2 (r s : ℕ) (δ : ℤ) (lamL lamR muL muR : YoungDiagram)
    (hlamL : lamL.colLen 0 ≤ r) (hlamR : lamR.colLen 0 ≤ s)
    (hmuL : muL.colLen 0 ≤ r) (hmuR : muR.colLen 0 ≤ s)
    (w : Equiv.Perm (Fin r ⊕ Fin s))
    (hw : weight r s muL muR = dotAct r s δ w (weight r s lamL lamR)) :
    IsBalanced δ lamL lamR muL muR := by sorry

end WalledBrauer.Blocks
