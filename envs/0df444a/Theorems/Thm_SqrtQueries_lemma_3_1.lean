-- Prove2me | Theorems.Thm_SqrtQueries_lemma_3_1
-- name    : SqrtQueries.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T13:29:15.482203+00:00
-- url     : https://prove2.me/theorems/65c4aa26-8743-43a1-a995-df4626bbebb6
-- title:
--   Lemma 3.1 (existential statement) — a square root has a discontinuity $\mu_{j^*+1}=-\omega_{2N}\mu_{j^*}$
-- statement:
--   Let $N\ge1$ and $\omega_N=e^{2\pi i/N}$. Let $U$ be an $N\times N$ complex matrix with eigenvalues $\lambda_j=\phi\,\omega_N^{\,j}$ ($j=0,\dots,N-1$), where $|\phi|=1$, and corresponding eigenvectors $u_0,\dots,u_{N-1}$. Let $V$ be any square root of $U$, $V^2=U$, whose eigenvalue at $u_j$ is $\mu_j$. Then there is an index $j^*$ with
--   $$
--   \mu_{j^*+1}=-\omega_{2N}\,\mu_{j^*},
--   $$
--   where $j^*+1$ is taken modulo $N$.
--
--   Every square root breaks the cyclic continuity of the spectrum somewhere; this discontinuity is what the square-root oracle reveals.
--
--   **Formalization Note** Eigenvectors are nonzero vectors $u_j$ with $Uu_j=\phi\omega_N^ju_j$ and $Vu_j=\mu_ju_j$. The algorithmic clauses of Lemma 3.1 ("Moreover, …") are not part of this statement.
--
--   Differences from the source:
--   - generalization: U a unitary whose eigenvectors are u_0, …, u_{N−1} → U any complex matrix with nonzero vectors u_j satisfying U u_j = φ ω_N^j u_j (not required to form a basis); reason: the existential argument uses only the eigen-relations; a unitary U with these eigenvectors is a special case
--   - encoding: j* + 1 mod N → Fin N addition; reason: Fin N addition is addition modulo N
-- source:
--   Ma–Tang, Square-root queries can help, STOC 2027 submission (manuscript sha256 783868e7…c5f15a), Lemma 3.1, p.14

import Mathlib
import Definitions.Def_MagnonCode_AQEDC_omega

namespace SqrtQueries

open Matrix

/-- **Lemma 3.1** (Efficiently locating discontinuities in square roots), existential statement,
of Ma–Tang, *Square-root queries can help*, STOC 2027 submission manuscript (sha256 783868e7…c5f15a), p.14. Let `U` have eigenvalues `λ_j = φ ω_N^j` (`|φ| = 1`) with eigenvectors
`u_0, …, u_{N−1}`, and let `V` be any square root of `U` (`V² = U`) whose eigenvalue at `u_j`
is `μ_j`. Then there is an index `j*` with `μ_{j*+1} = −ω_{2N} μ_{j*}` (`j* + 1` modulo `N`).

**Formalization Note.** `j* + 1` is `Fin N` addition (modulo `N`). The eigenvectors are nonzero
vectors `u j` with `U u_j = φ ω_N^j u_j` and `V u_j = μ_j u_j`; `U` is not required to be
unitary and the `u_j` are not required to form a basis (a generalization). The algorithmic
clauses of the lemma ("Moreover, …") are not part of this item. -/
theorem lemma_3_1 (N : ℕ) [NeZero N] (U V : Matrix (Fin N) (Fin N) ℂ) (φ : ℂ) (hφ : ‖φ‖ = 1)
    (u : Fin N → Fin N → ℂ) (hu : ∀ j, u j ≠ 0)
    (hU : ∀ j, U *ᵥ u j = (φ * MagnonCode.AQEDC.omega N ^ (j : ℕ)) • u j) (hV : V * V = U) (μ : Fin N → ℂ)
    (hμ : ∀ j, V *ᵥ u j = μ j • u j) :
    ∃ jstar : Fin N, μ (jstar + 1) = -MagnonCode.AQEDC.omega (2 * N) * μ jstar := by sorry

end SqrtQueries
