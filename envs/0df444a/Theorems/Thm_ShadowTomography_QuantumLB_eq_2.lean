-- Prove2me | Theorems.Thm_ShadowTomography_QuantumLB_eq_2
-- name    : ShadowTomography.QuantumLB.eq_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T01:13:41.36253+00:00
-- url     : https://prove2.me/theorems/eca4a131-fc12-41e9-a583-0943e7cdccaf
-- title:
--   Eq. (2) — ⌊c^{N²}⌋ half-dimensional projections with $|\operatorname{Tr}(\mathbb P_i\rho_j)-1/2|\le 1/12$
-- statement:
--   For a projection $\mathbb P$ onto an $N/2$-dimensional subspace of $\mathbb C^N$ write $\rho_{\mathbb P} = \tfrac2N\mathbb P$ for the maximally mixed state on that subspace.
--
--   There is a constant $c\in(1,2)$ and a threshold $N_0$ such that for every even $N\ge N_0$, with $K:=\lfloor c^{N^2}\rfloor$, there exist orthogonal projections $\mathbb P_1,\dots,\mathbb P_K$ onto $N/2$-dimensional subspaces $S_1,\dots,S_K\le\mathbb C^N$ such that, writing $\rho_j=\tfrac2N\mathbb P_j$,
--
--   $$
--   \Bigl|\operatorname{Tr}(\mathbb P_i\rho_j) - \frac12\Bigr| \le \frac1{12} \qquad\text{for all } i\neq j .
--   $$
--
--   Since $\operatorname{Tr}(\mathbb P_i\rho_j) = \tfrac2N\operatorname{Tr}(\mathbb P_i\mathbb P_j)$, this says that exponentially many $N/2$-dimensional subspaces can be chosen pairwise "nearly as far apart as random". These subspaces give the $K$ measurements and the $K$ hard states of the lower bound.
--
--   **Formalization Note** The paper asserts that independent Haar-random subspaces satisfy (2) with probability $1-o(1)$, and then fixes such a choice. Mathlib has no Haar measure on the Grassmannian (or on the unitary group), so the statement is the existence of such subspaces, which is exactly what the proof of Theorem 19 uses. The $c$ and the threshold $N_0$ formalize "for some constant $c\in(1,2)$ … as long as $c$ is sufficiently small" and the asymptotic $1-o(1)$.
-- source:
--   Aaronson, Shadow Tomography of Quantum States, arXiv:1711.01053v2, p. 23, proof of Theorem 19, Eq. (2)

import Mathlib
import Definitions.Def_ShadowTomography_QuantumLB_IsHalfProjector
import Definitions.Def_ShadowTomography_QuantumLB_rhoState

namespace ShadowTomography.QuantumLB

/-- Eq. (2), existence form: for some `c ∈ (1, 2)` and all large even `N` there are
`K = ⌊c^{N²}⌋` projectors `ℙ_i` onto `N/2`-dimensional subspaces of `ℂ^N` with
`|Tr(ℙ_i ρ_j) − 1/2| ≤ 1/12` for all `i ≠ j`, where `ρ_j = (2/N) ℙ_j`. -/
theorem eq_2 :
    ∃ c : ℝ, 1 < c ∧ c < 2 ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      ∃ P : Fin ⌊c ^ (N ^ 2)⌋₊ → Matrix (Fin N) (Fin N) ℂ,
        (∀ i, IsHalfProjector (P i)) ∧
        ∀ i j, i ≠ j → |(P i * rhoState (P j)).trace.re - 1 / 2| ≤ 1 / 12 := by sorry

end ShadowTomography.QuantumLB
