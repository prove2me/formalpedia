-- Prove2me | Theorems.Thm_SteuerChoo_Discrete_theorem_3_1
-- name    : SteuerChoo.Discrete.theorem_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:45:01.505013+00:00
-- url     : https://prove2.me/theorems/a54fdd8c-68c6-498c-ac94-7bebc29bb118
-- title:
--   Theorem 3.1 — some minimizer of the weighted Tchebycheff program over a finite Z is nondominated
-- statement:
--   Let $k \ge 1$, let $Z \subset \mathbb R^k$ be a nonempty finite set of criterion vectors with nondominated set $N$, let $\lambda \in \bar\Lambda = \{\lambda \in \mathbb R^k \mid \lambda_i \ge 0,\ \sum_i \lambda_i = 1\}$ and $z^* \in \mathbb R^k$. Let
--   $$M = \Big\{ z \in Z \;\Big|\; \max_i \lambda_i (z^*_i - z_i) \le \max_i \lambda_i (z^*_i - z'_i) \text{ for all } z' \in Z \Big\}$$
--   be the set of minimizers of the weighted Tchebycheff program over $Z$. Then there exists $\bar z \in M$ with $\bar z \in N$.
--
--   The weighted Tchebycheff program can have several minimal solutions, some of them dominated; the theorem guarantees that the tie always contains a nondominated vector.
--
--   **Formalization Note** $S$, $f$ and the program variable $\alpha$ are eliminated: the minimal $\alpha$ at $z$ is $\max_i \lambda_i(z^*_i - z_i)$. The statement holds for every reference vector $z^*$, so no ideal-vector hypothesis is imposed (the paper's $z^*$ is ideal, a special case). Nonemptiness of $Z$ and $k \ge 1$ are the paper's implicit assumptions.
-- source:
--   Steuer and Choo, An Interactive Weighted Tchebycheff Procedure for Multiple Objective Programming, Math. Programming 26 (1983) 326–344, https://doi.org/10.1007/BF02591870, p. 330, Theorem 3.1

import Mathlib
import Definitions.Def_SteuerChoo_Discrete_Nondominated
import Definitions.Def_SteuerChoo_Discrete_Tchebycheff

namespace SteuerChoo.Discrete

/-- **Theorem 3.1** (Steuer–Choo 1983, p. 330): let `Z` be finite and let `M` be the set of
`z ∈ Z` minimizing the weighted Tchebycheff program. Then some `z̄ ∈ M` is nondominated.
Here `Z` is a nonempty finite set of criterion vectors, `λ ∈ Λ̄` and `z*` is arbitrary. -/
theorem theorem_3_1 {k : ℕ} [NeZero k] (Z : Finset (Fin k → ℝ)) (hZ : Z.Nonempty)
    (lam : Fin k → ℝ) (hlam : lam ∈ stdSimplex ℝ (Fin k)) (zstar : Fin k → ℝ) :
    ∃ zbar ∈ Z, (∀ z ∈ Z, tcheb lam zstar zbar ≤ tcheb lam zstar z) ∧ zbar ∈ nondominated Z := by sorry

end SteuerChoo.Discrete
