-- Prove2me | Theorems.Thm_SteuerChoo_Lexico_lexMin_unique_of_nondominated
-- name    : SteuerChoo.Lexico.lexMin_unique_of_nondominated
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:53:06.927987+00:00
-- url     : https://prove2.me/theorems/e754eed3-36d1-46ca-9c94-954f129fab9a
-- title:
--   Theorem 4.5 — each $\bar z\in N$ uniquely minimizes the lexicographic weighted Tchebycheff program for $\bar\lambda$ of (4.3)
-- statement:
--   Let $Z\subseteq\mathbb R^k$ ($k\ge1$) be a compact set of criterion vectors with nondominated set $N$, let $z^*$ be an ideal criterion vector for $Z$, and let $\bar z\in N$. Let $\bar\lambda$ be the weights of eq. (4.3) for $\bar z$. Then $\bar\lambda\in\bar\Lambda=\{\lambda\in\mathbb R^k\mid \lambda_i\ge0,\ \sum_i\lambda_i=1\}$, and $\bar z$ uniquely minimizes the lexicographic weighted Tchebycheff program
--   $$
--   \operatorname{lex\,min}\ \big\{P_1\,\alpha+P_2\,e^{\mathsf T}(z^*-z)\big\}\quad\text{s.t.}\quad\alpha\ge\bar\lambda_i(z^*_i-z_i),\ 1\le i\le k,\quad z\in Z:
--   $$
--   $\bar z$ is a lexicographic minimizer, and every lexicographic minimizer equals $\bar z$.
--
--   So every nondominated criterion vector is computable, uniquely, by the lexicographic weighted Tchebycheff program, whatever the shape of the feasible region.
--
--   **Formalization Note** The paper states "there exists a $\bar\lambda\in\bar\Lambda$"; its proof ends "for $\bar\lambda$ as defined in (4.3)", and the statement here exhibits that witness, which implies the existential form. **Compactness of $Z$ is an added hypothesis.** The paper assumes only $S$ bounded; its proof, in the case $\bar z_j=z^*_j$, needs every first-stage minimizer to lie below some nondominated vector, which compactness provides. Without closedness the witness (4.3) can fail: $Z=\{(5,3,0),(0,10,0),(0,0,6)\}\cup\{(5,0,4+t):0\le t<1\}$, $z^*=(5,10,6)$, $\bar z=(5,3,0)$, $\bar\lambda=(1,0,0)$ has no lexicographic minimizer. Closedness is needed by the theorem itself, not only by this proof: adding the points $(5-s^2,\,3+s,\,0)$, $0<s\le1$, to that $Z$ (still bounded, $\varepsilon=0$ still admissible) leaves $\bar z=(5,3,0)\in N$ a lexicographic minimizer for no $\lambda\in\bar\Lambda$, so Theorems 4.5 and 4.6 are false for a bounded, non-closed $Z$. The priority "$P_1<<<P_2$" is printed reversed; the two-stage meaning of p. 336 is encoded (see the definition `IsLexMin`). "Uniquely" refers to the criterion vector; $x$ and $\alpha$ are eliminated.
-- source:
--   Steuer and Choo, An Interactive Weighted Tchebycheff Procedure for Multiple Objective Programming, Math. Programming 26 (1983), p. 335, Theorem 4.5 (with the witness of eq. (4.3), p. 334, as in the proof, p. 336)

import Mathlib
import Definitions.Def_SteuerChoo_Lexico_nondominated
import Definitions.Def_SteuerChoo_Lexico_IsIdealVector
import Definitions.Def_SteuerChoo_Lexico_lamBar
import Definitions.Def_SteuerChoo_Lexico_IsLexMin

namespace SteuerChoo.Lexico

theorem lexMin_unique_of_nondominated {k : ℕ} [NeZero k]
    (Z : Set (Fin k → ℝ)) (zstar zbar : Fin k → ℝ)
    (hZc : IsCompact Z) (hideal : IsIdealVector Z zstar)
    (hzbar : zbar ∈ nondominated Z) :
    lamBar zstar zbar ∈ stdSimplex ℝ (Fin k) ∧
      IsLexMin Z (lamBar zstar zbar) zstar zbar ∧
      ∀ w, IsLexMin Z (lamBar zstar zbar) zstar w → w = zbar := by sorry

end SteuerChoo.Lexico
