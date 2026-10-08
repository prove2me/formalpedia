-- Prove2me | Theorems.Thm_QueueingFundamentals_Numerical_stationary_iff
-- name    : QueueingFundamentals.Numerical.stationary_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T20:24:55.617697+00:00
-- url     : https://prove2.me/theorems/3d2d2871-27f0-47c8-9d80-ac5eec48ca81
-- title:
--   Stationary equations of the uniformized chain: $\phi = \phi\tilde P \iff 0 = \phi Q$ (p.385)
-- statement:
--   Let $Q$ be an $(N+1)\times(N+1)$ real matrix, $\Lambda>0$, and $\tilde P=Q/\Lambda+I$. For every row vector $\phi$,
--
--   $$\phi=\phi\tilde P\iff 0=\phi Q.$$
--
--   Hence the uniformized imbedded chain with transition matrix $\tilde P$ and the continuous-time chain with generator $Q$ have the same stationary equations, so randomization can also be used to compute steady-state distributions.
--
--   **Formalization Note** The book displays the chain of implications from left to right; both directions hold and are stated. The book's intermediate step prints $\phi(Q/\Lambda - I)$ where $\phi(Q/\Lambda + I)$ is meant. The accompanying sentence also asserts $\lim_{k\to\infty}\phi^{(k)}=\lim_{t\to\infty}p(t)$; that limit statement is not part of this item, since $\phi^{(k)}$ need not converge when $\tilde P$ is periodic (possible when $\Lambda=\max_i q_i$).
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.385, §8.1.2.2 (unnumbered display φ = φP̃ ⇒ … ⇒ 0 = φQ)

import Mathlib
import Definitions.Def_QueueingFundamentals_Numerical_Uniformization

open Matrix

namespace QueueingFundamentals.Numerical

/-- The steady-state equivalence of p.385 (Gross et al., §8.1.2.2, unnumbered display): for
`Λ > 0` and a row vector `φ`, `φ = φP̃` if and only if `0 = φQ`, where `P̃ = Q/Λ + I`. So the
uniformized chain and the continuous-time chain have the same stationary equations. -/
theorem stationary_iff {N : ℕ} (Q : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (Λ : ℝ) (hΛ : 0 < Λ) (φ : Fin (N + 1) → ℝ) :
    φ = φ ᵥ* uniformizedMatrix Λ Q ↔ φ ᵥ* Q = 0 := by sorry

end QueueingFundamentals.Numerical
