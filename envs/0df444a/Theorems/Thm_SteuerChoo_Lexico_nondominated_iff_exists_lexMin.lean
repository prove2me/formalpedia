-- Prove2me | Theorems.Thm_SteuerChoo_Lexico_nondominated_iff_exists_lexMin
-- name    : SteuerChoo.Lexico.nondominated_iff_exists_lexMin
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:50:53.866553+00:00
-- url     : https://prove2.me/theorems/b8a94d4b-6492-4bcf-ab4e-974c5997e28c
-- title:
--   Theorem 4.6 — $\bar z\in N$ iff $\bar z$ minimizes the lexicographic weighted Tchebycheff program for some $\lambda\in\bar\Lambda$
-- statement:
--   Let $Z\subseteq\mathbb R^k$ ($k\ge1$) be a compact set of feasible criterion vectors with nondominated set $N$, and let $z^*$ be an ideal criterion vector for $Z$. For every $\bar z\in Z$,
--   $$
--   \bar z\in N\iff \exists\,\lambda\in\bar\Lambda \text{ such that } \bar z \text{ minimizes }\ \operatorname{lex\,min}\big\{P_1\,\alpha+P_2\,e^{\mathsf T}(z^*-z)\big\}\ \text{s.t.}\ \alpha\ge\lambda_i(z^*_i-z_i),\ 1\le i\le k,\ z\in Z,
--   $$
--   where $\bar\Lambda=\{\lambda\in\mathbb R^k\mid\lambda_i\ge0,\ \sum_i\lambda_i=1\}$ and the lexicographic program first minimizes $\alpha=\max_i\lambda_i(z^*_i-z_i)$ and then, among the first-stage minimizers, minimizes $e^{\mathsf T}(z^*-z)=\sum_i(z^*_i-z_i)$.
--
--   The lexicographic weighted Tchebycheff program therefore characterizes the nondominated set for an arbitrary (in particular nonconvex, continuous) feasible region, without choosing an augmentation parameter $\rho$.
--
--   **Formalization Note** $S$, the objectives $f_i$ and the variable $\alpha$ are eliminated: $Z$ is the set of criterion vectors. **Compactness of $Z$ is an added hypothesis**, used by the direction $\Rightarrow$ (through Theorem 4.5); the paper assumes $S$ bounded. It is not removable: for a bounded but non-closed $Z$ the direction $\Rightarrow$ can fail (example in the Formalization Note of Theorem 4.5). The direction $\Leftarrow$ holds without it. The printed priority "$P_1<<<P_2$" is reversed relative to the paper's two-stage description on p. 336, which is what is encoded.
-- source:
--   Steuer and Choo, An Interactive Weighted Tchebycheff Procedure for Multiple Objective Programming, Math. Programming 26 (1983), p. 336, Theorem 4.6

import Mathlib
import Definitions.Def_SteuerChoo_Lexico_nondominated
import Definitions.Def_SteuerChoo_Lexico_IsIdealVector
import Definitions.Def_SteuerChoo_Lexico_IsLexMin

namespace SteuerChoo.Lexico

theorem nondominated_iff_exists_lexMin {k : ℕ} [NeZero k]
    (Z : Set (Fin k → ℝ)) (zstar zbar : Fin k → ℝ)
    (hZc : IsCompact Z) (hideal : IsIdealVector Z zstar) (hzbar : zbar ∈ Z) :
    zbar ∈ nondominated Z ↔
      ∃ lam ∈ stdSimplex ℝ (Fin k), IsLexMin Z lam zstar zbar := by sorry

end SteuerChoo.Lexico
