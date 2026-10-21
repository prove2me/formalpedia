-- Prove2me | Theorems.Thm_ProConChoice_Rational_step_2
-- name    : ProConChoice.Rational.step_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:04:24.126078+00:00
-- url     : https://prove2.me/theorems/66bb4bc5-74db-4bb8-a3df-a69b33cdbb51
-- title:
--   Step 2 of the proof of Theorem 2, eq. (25), p. 21 — the column sums Σ_{x∈S} q(x,S) equal the row sums Σᵢ λₖ([≻ᵏᵢ])
-- statement:
--   Let $X$ be a finite set with $n$ elements, $p$ a random choice function on $X$, $1 \le k \le n - 1$, and $\lambda_k$ a signed weight function on the $k$-prefixes that represents $p_k$. Let $S$ be a choice set with $|S| = n - k$, and let $[\succ^k_1], \dots, [\succ^k_{k!}]$ be the $k$-prefixes that order the $k$ alternatives of $X \setminus S$. Then
--   $$\sum_{x_j \in S} q(x_j, S) = \sum_{i=1}^{k!} \lambda_k([\succ^k_i]), \qquad (25)$$
--   where $q$ is the Möbius transform (9) of $p$.
--
--   Equation (25) says that the row data and the column data of the system (RS)–(CS) at $S$ have the same total, the first hypothesis of the generalized Ford–Fulkerson theorem.
--
--   **Formalization Note** The $k$-prefixes ordering $X \setminus S$ are the injections `Fin k ↪ X` whose values all lie outside $S$ (there are exactly $k!$ of them, since $|X \setminus S| = k$). $|S| = n - k$ is written $|S| + k = n$.
-- source:
--   Dogan & Yildiz, Every choice function is pro-con rationalizable, SSRN 3085542 (January 10, 2021), p. 21, Step 2 of the proof of Theorem 2, eq. (25)

import Mathlib
import Definitions.Def_ProConChoice_Rational_RandomChoice

namespace ProConChoice.Rational

/-- Step 2 of the proof of Theorem 2, eq. (25) (p. 21): for a random choice function `p`,
`1 ≤ k ≤ n - 1`, `λₖ` representing `pₖ`, and `|S| = n - k`, the column sums equal the row sums:
`∑_{x ∈ S} q(x, S) = ∑ λₖ([≻ᵏ])` over the `k`-prefixes ordering exactly `X \ S`. -/
theorem step_2 {X : Type*} [Fintype X] [DecidableEq X]
    (p : X → Finset X → ℝ) (hp : IsRCF p) (k : ℕ) (hk : 1 ≤ k) (hkn : k < Fintype.card X)
    (lam : (Fin k ↪ X) → ℝ) (hrep : Represents k lam p)
    (S : Finset X) (hS : S.card + k = Fintype.card X) :
    ∑ x ∈ S, mobiusQ p x S =
      ∑ π ∈ (Finset.univ : Finset (Fin k ↪ X)).filter (fun π => ∀ i, π i ∉ S), lam π := by sorry

end ProConChoice.Rational
