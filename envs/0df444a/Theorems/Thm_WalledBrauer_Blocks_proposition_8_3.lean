-- Prove2me | Theorems.Thm_WalledBrauer_Blocks_proposition_8_3
-- name    : WalledBrauer.Blocks.proposition_8_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:43:20.750605+00:00
-- url     : https://prove2.me/theorems/a15bf915-63eb-46c6-846f-dbabc7dceaed
-- title:
--   Proposition 8.3 — $\delta$-balanced bipartitions lie in one orbit of the $\rho(\delta)$-shifted dot action
-- statement:
--   Let $r,s\in\mathbb N$ and $\delta\in\mathbb Z$. Let $(\lambda^L,\lambda^R)$ and $(\mu^L,\mu^R)$ be bipartitions with at most $r$ and $s$ rows respectively. If they are $\delta$-balanced, then there exists $w\in W=\Sigma_{r+s}$ with
--   $$
--   (\bar\mu^L;\mu^R)=w.(\bar\lambda^L;\lambda^R),
--   $$
--   where $w.v=w(v+\rho(\delta))-\rho(\delta)$, $\rho(\delta)=(r,\dots,1;\delta,\dots,\delta-s+1)$, and $(\bar\lambda^L;\lambda^R)$ is the embedding (23).
--
--   Together with Proposition 8.2, this identifies balance with orbit membership.
--
--   **Formalization Note** "At most $r$ rows" is `λ.colLen 0 ≤ r`. $W$ is `Equiv.Perm (Fin r ⊕ Fin s)`, acting by $(wv)(x)=v(w^{-1}x)$.
-- source:
--   Cox, De Visscher, Doty & Martin, On the blocks of the walled Brauer algebra, arXiv:0709.0851v1, p. 34, Proposition 8.3

import Mathlib
import Definitions.Def_WalledBrauer_Blocks_Partitions
import Definitions.Def_WalledBrauer_Blocks_Weights

namespace WalledBrauer.Blocks

/-- Proposition 8.3 (p. 34). Let `δ ∈ ℤ` and let `(λL, λR)`, `(μL, μR)` be bipartitions with at
most `r` and `s` rows. If they are `δ`-balanced then there exists `w ∈ W = Σ_{r+s}` such that
`(μ̄L; μR) = w.(λ̄L; λR)` (dot action with respect to `ρ(δ)`). -/
theorem proposition_8_3 (r s : ℕ) (δ : ℤ) (lamL lamR muL muR : YoungDiagram)
    (hlamL : lamL.colLen 0 ≤ r) (hlamR : lamR.colLen 0 ≤ s)
    (hmuL : muL.colLen 0 ≤ r) (hmuR : muR.colLen 0 ≤ s)
    (h : IsBalanced δ lamL lamR muL muR) :
    ∃ w : Equiv.Perm (Fin r ⊕ Fin s), weight r s muL muR = dotAct r s δ w (weight r s lamL lamR) := by sorry

end WalledBrauer.Blocks
