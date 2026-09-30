-- Prove2me | Theorems.Thm_SteuerChoo_Lexico_lexMin_exists_and_nondominated
-- name    : SteuerChoo.Lexico.lexMin_exists_and_nondominated
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:50:06.12347+00:00
-- url     : https://prove2.me/theorems/d9e5d52c-1520-424b-ac9f-e5fea52fbee1
-- title:
--   §4, p. 336 — the lexicographic program has a solution, and every solution is nondominated
-- statement:
--   Let $Z\subseteq\mathbb R^k$ ($k\ge1$), $z^*\in\mathbb R^k$ and weights $\lambda\in\bar\Lambda=\{\lambda\in\mathbb R^k\mid \lambda_i\ge0,\ \sum_i\lambda_i=1\}$. Then:
--
--   1. if $Z$ is compact and nonempty, the lexicographic weighted Tchebycheff program with weights $\lambda$ has a minimizer;
--   2. every minimizer $z$ of the lexicographic weighted Tchebycheff program with weights $\lambda$ is nondominated:
--   $$
--   z \text{ lexicographically minimizes } \big(\max_i\lambda_i(z^*_i-z_i),\ e^{\mathsf T}(z^*-z)\big) \text{ over } Z\ \Longrightarrow\ z\in N .
--   $$
--
--   This makes precise the remark that if the first-stage minimization of $\alpha$ does not yield a nondominated vector, the second-stage minimization of $e^{\mathsf T}(z^*-z)$ moves to one that is.
--
--   **Formalization Note** Part 1 uses compactness of $Z$, an added hypothesis (the paper assumes $S$ bounded and speaks of minimizers). Part 2 needs neither compactness nor the ideal-vector property, and $z^*$ is arbitrary in both parts.
-- source:
--   Steuer and Choo, An Interactive Weighted Tchebycheff Procedure for Multiple Objective Programming, Math. Programming 26 (1983), p. 336, §4, paragraph after Theorem 4.6

import Mathlib
import Definitions.Def_SteuerChoo_Lexico_nondominated
import Definitions.Def_SteuerChoo_Lexico_IsLexMin

namespace SteuerChoo.Lexico

theorem lexMin_exists_and_nondominated {k : ℕ} [NeZero k]
    (Z : Set (Fin k → ℝ)) (zstar lam : Fin k → ℝ)
    (hlam : lam ∈ stdSimplex ℝ (Fin k)) :
    (IsCompact Z → Z.Nonempty → ∃ z, IsLexMin Z lam zstar z) ∧
      ∀ z, IsLexMin Z lam zstar z → z ∈ nondominated Z := by sorry

end SteuerChoo.Lexico
