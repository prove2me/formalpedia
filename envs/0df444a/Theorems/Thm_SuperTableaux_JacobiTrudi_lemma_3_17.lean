-- Prove2me | Theorems.Thm_SuperTableaux_JacobiTrudi_lemma_3_17
-- name    : SuperTableaux.JacobiTrudi.lemma_3_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:29:58.831019+00:00
-- url     : https://prove2.me/theorems/e9595430-8dbe-4a81-aebc-097a4e2e53d9
-- title:
--   Lemma 3.17, p. 17 — $\{S^{\mathcal A}_\lambda:\lambda\in\mathscr P_{\mathcal A}\}$ is linearly independent over $\mathbb Z$
-- statement:
--   Let $\mathcal A$ be a linearly ordered, at most countable, $\mathbb Z_2$-graded set and $\mathscr P_{\mathcal A}$ the set of partitions $\lambda$ with $SST_{\mathcal A}(\lambda)\neq\emptyset$. Then the family
--   $$\{\,S^{\mathcal A}_\lambda\;:\;\lambda\in\mathscr P_{\mathcal A}\,\}\subset\mathbb Z[[x_{\mathcal A}]]$$
--   is linearly independent over $\mathbb Z$.
--
--   For finite $\mathcal A$ these are hook Schur polynomials; the lemma is the basis of every uniqueness-of-coefficients argument in the paper.
--
--   **Formalization Note** Partitions are Mathlib's `YoungDiagram`; $S^{\mathcal A}_\lambda$ is `MvPowerSeries A ℤ` with coefficient at $x^m$ the number of $\mathcal A$-semistandard tableaux of shape $\lambda$ and weight $m$. Linear independence is Mathlib's `LinearIndependent ℤ` (finite combinations), as in the paper's proof.
-- source:
--   Kwon, Rational semistandard tableaux and character formula for the Lie superalgebra ĝl∞|∞, arXiv:math/0605005v1, p. 17, Lemma 3.17

import Mathlib
import Definitions.Def_SuperTableaux_JacobiTrudi_Setting

namespace SuperTableaux.JacobiTrudi
theorem lemma_3_17 {A : Type*} [LinearOrder A] [Countable A] (oddA : A → Bool) :
    LinearIndependent ℤ
      (fun la : {la : YoungDiagram // Nonempty (SSF oddA la)} => charA oddA la.1) := by sorry
end SuperTableaux.JacobiTrudi
