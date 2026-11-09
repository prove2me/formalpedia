-- Prove2me | Theorems.Thm_SqrtQueries_sqrt_clock
-- name    : SqrtQueries.sqrt_clock
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T13:30:00.753681+00:00
-- url     : https://prove2.me/theorems/f81cd291-d03b-4225-9972-bf9389582a39
-- title:
--   Section 2.1 — the square roots of $D$ are $\Sigma B$, $B=\operatorname{diag}(\omega_{2N}^j)$
-- statement:
--   Let $N\ge1$ and let $D=\sum_j\omega_N^j|j\rangle\langle j|$ be the clock operator. A complex $N\times N$ matrix $V$ satisfies $V^2=D$ if and only if
--   $$
--   V=\Sigma B,\qquad B=\sum_{j=0}^{N-1}\mu_j|j\rangle\langle j|,\quad \mu_j=e^{\pi i j/N}=\omega_{2N}^{\,j},
--   $$
--   for some diagonal matrix $\Sigma$ of signs $\pm1$.
--
--   A generic square root of $D$ is written $R=\Sigma B$; it is the starting point of the analysis of the roots of $U_1=e^{iA/4}De^{-iA/4}$.
--
--   Differences from the source: none.
-- source:
--   Ma–Tang, Square-root queries can help, STOC 2027 submission (manuscript sha256 783868e7…c5f15a), Section 2.1, p.10

import Mathlib
import Definitions.Def_SqrtQueries_clockOp

namespace SqrtQueries

/-- **Square roots of the clock operator** (Section 2.1 of Ma–Tang, *Square-root queries can help*, STOC 2027 submission manuscript (sha256 783868e7…c5f15a), p.10): "the set of square roots of
`D` consist of the matrices `ΣB`, where `Σ` is any diagonal matrix of signs and
`B = ∑_{j=0}^{N−1} μ_j |j⟩⟨j|`, `μ_j = e^{πij/N} = ω_{2N}^j`".

**Formalization Note.** For every `N ≥ 1` (`[NeZero N]`); a square root is any complex matrix
`V` with `V * V = D`, and `ω_{2N}` is `MagnonCode.AQEDC.omega (2 * N)`. -/
theorem sqrt_clock (N : ℕ) [NeZero N] (V : Matrix (Fin N) (Fin N) ℂ) :
    V * V = clockOp N ↔
      ∃ σ : Fin N → ℂ, (∀ j, σ j = 1 ∨ σ j = -1) ∧
        V = Matrix.diagonal σ * Matrix.diagonal (fun j : Fin N => MagnonCode.AQEDC.omega (2 * N) ^ (j : ℕ)) := by sorry

end SqrtQueries
