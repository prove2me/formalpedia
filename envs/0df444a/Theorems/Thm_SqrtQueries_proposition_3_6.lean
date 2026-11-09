-- Prove2me | Theorems.Thm_SqrtQueries_proposition_3_6
-- name    : SqrtQueries.proposition_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T13:31:26.308207+00:00
-- url     : https://prove2.me/theorems/e971c2f3-d4e6-407f-96d0-07e987572c76
-- title:
--   Proposition 3.6 — $\|V_0-V_1\|\ge1/10$ for any roots of $U_0$, $U_1$
-- statement:
--   Let $N\ge4$ and let $U_0$, $U_1$ be the oracles of Definition 3.2. For any square roots $V_0$ of $U_0$ and $V_1$ of $U_1$ ($V_0^2=U_0$, $V_1^2=U_1$),
--   $$
--   \|V_0-V_1\|\ge\frac1{10}
--   $$
--   in operator norm.
--
--   Although $U_0$ and $U_1$ are $O(1/N)$-close (Proposition 3.5), their square roots are a constant apart, whichever roots are taken; square-root queries amplify the difference.
--
--   **Formalization Note** A square root is any complex matrix $V$ with $VV=U_b$.
--
--   Differences from the source: none.
-- source:
--   Ma–Tang, Square-root queries can help, STOC 2027 submission (manuscript sha256 783868e7…c5f15a), Proposition 3.6, p.17

import Mathlib
import Definitions.Def_SqrtQueries_oracle

open scoped Matrix.Norms.L2Operator

namespace SqrtQueries

/-- **Proposition 3.6** (Distinguishing is possible with roots) of Ma–Tang, *Square-root queries can help*, STOC 2027 submission manuscript (sha256 783868e7…c5f15a), p.17: for `N ≥ 4` and any
square roots `V₀` of `U₀` and `V₁` of `U₁` (Definition 3.2), `‖V₀ − V₁‖ ≥ 1/10`.

**Formalization Note.** A square root of `U_b` is any complex matrix `V` with `V * V = U_b`;
`‖·‖` is the `L2` operator norm (`Matrix.Norms.L2Operator`). -/
theorem proposition_3_6 (N : ℕ) [NeZero N] (hN : 4 ≤ N) (V₀ V₁ : Matrix (Fin N) (Fin N) ℂ)
    (h₀ : V₀ * V₀ = oracle N false) (h₁ : V₁ * V₁ = oracle N true) :
    1 / 10 ≤ ‖V₀ - V₁‖ := by sorry

end SqrtQueries
