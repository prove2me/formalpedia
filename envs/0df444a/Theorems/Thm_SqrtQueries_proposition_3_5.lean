-- Prove2me | Theorems.Thm_SqrtQueries_proposition_3_5
-- name    : SqrtQueries.proposition_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T13:31:35.977805+00:00
-- url     : https://prove2.me/theorems/0d96a59b-63ff-48bf-9577-f89caa500b45
-- title:
--   Proposition 3.5 — $\|U_0-U_1\|\le\pi/(2N)$
-- statement:
--   Let $N\ge1$ and let $U_0=D$ and $U_1=e^{iA/4}De^{-iA/4}$ be the oracles of Definition 3.2 on $\mathbb C^N$. Then
--   $$
--   \|U_0-U_1\|\le\frac{\pi}{2N},
--   $$
--   where $\|\cdot\|$ is the operator norm.
--
--   This is the source of the lower bound: the two oracles are so close that a query algorithm needs about $N$ queries to tell them apart.
--
--   **Formalization Note** $\|\cdot\|$ is the operator norm induced by the Euclidean norm on $\mathbb C^N$.
--
--   Differences from the source: none.
-- source:
--   Ma–Tang, Square-root queries can help, STOC 2027 submission (manuscript sha256 783868e7…c5f15a), Proposition 3.5, p.17

import Mathlib
import Definitions.Def_SqrtQueries_oracle

open scoped Matrix.Norms.L2Operator

namespace SqrtQueries

/-- **Proposition 3.5** (Distinguishing is hard without roots) of Ma–Tang, *Square-root queries can help*, STOC 2027 submission manuscript (sha256 783868e7…c5f15a), p.17: for the oracle pair
`U₀ = D`, `U₁ = e^{iA/4} D e^{−iA/4}` of Definition 3.2, `‖U₀ − U₁‖ ≤ π/(2N)`.

**Formalization Note.** `‖·‖` is the operator norm induced by the Euclidean norm on `ℂ^N`
(`Matrix.Norms.L2Operator`). The statement is for every `N ≥ 1` (`[NeZero N]`); Definition 3.2
puts no lower bound on `N`. -/
theorem proposition_3_5 (N : ℕ) [NeZero N] :
    ‖oracle N false - oracle N true‖ ≤ Real.pi / (2 * N) := by sorry

end SqrtQueries
