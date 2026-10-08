-- Prove2me | Theorems.Thm_TalagrandConc_Assignment_proposition_10_3
-- name    : TalagrandConc.Assignment.proposition_10_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:47:26.23363+00:00
-- url     : https://prove2.me/theorems/998df4fd-2cad-4f2e-9d5a-389f4013dd44
-- title:
--   Proposition 10.3 — the random digraph D_u is u log N-expanding with probability ≥ 1 − N^{−u/K}
-- statement:
--   Let the costs $X_{i,j}$, $i \in I$, $j \in J$, $|I| = |J| = N$, be independent and uniformly distributed on $[0,1]$, and for $u > 0$ let $D_u = \{(i,j) ;\ X_{i,j} \le 2uN^{-1}\log N\}$. There is a universal constant $K > 0$ such that for every $N \ge 1$ and every $u > K$ with $u \log N \le N$,
--   $$P\big(D_u \text{ is } u\log N\text{-expanding}\big) \ge 1 - N^{-u/K}.$$
--
--   Combined with Corollary 10.2, this shows that with high probability the optimal assignment only uses costs of order $N^{-1}(\log N)^2$.
--
--   **Formalization Note** $K$ is quantified before $N$ and $u$. The probability is the product law of the $N^2$ uniform costs; $1 - N^{-u/K}$ is computed in $[0,\infty]$. The paper's statement implicitly has $N \ge 1$; at $N = 1$ the right side is $0$ and the claim is trivial, and at $N = 0$ it would be false, so $N \ge 1$ is stated.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 167, Proposition 10.3

import Mathlib
import Definitions.Def_TalagrandConc_Assignment_Basic

namespace TalagrandConc.Assignment

open MeasureTheory

/-- Talagrand (1995), p. 167, Proposition 10.3. There is a universal constant `K > 0` such
that for every `N ≥ 1` and every `u > K` with `u log N ≤ N`, the random digraph `D_u`
(costs i.i.d. uniform on `[0, 1]`) is `u log N`-expanding with probability
`≥ 1 − N^{−u/K}`. -/
theorem proposition_10_3 :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, 1 ≤ N → ∀ u : ℝ, K < u → u * Real.log N ≤ N →
      1 - ENNReal.ofReal ((N : ℝ) ^ (-u / K)) ≤
        costLaw N {X | IsExpanding N (u * Real.log N) (digraphU N u X)} := by sorry

end TalagrandConc.Assignment
