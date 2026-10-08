-- Prove2me | Theorems.Thm_SoysterInexactLP_Auxiliary_lemma_X_convex
-- name    : SoysterInexactLP.Auxiliary.lemma_X_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:37:08.277014+00:00
-- url     : https://prove2.me/theorems/b146b8f2-6798-4d2d-8107-d255d97c6942
-- title:
--   LEMMA — the feasible set X of (I) is convex
-- statement:
--   Let $K_1,\dots,K_n\subseteq\mathbb R^m$ be nonempty convex activity sets and $K\subseteq\mathbb R^m$ a nonempty convex resource set. Then the feasible set of problem (I),
--   $$X=\{x\in\mathbb R^n \mid x_j\ge0\ \forall j,\ x_1K_1+\cdots+x_nK_n\subseteq K\},$$
--   is a convex subset of $\mathbb R^n$.
--
--   Together with the linear objective, this makes (I) a convex program.
--
--   **Formalization Note** All four standing assumptions of p. 1154 are hypotheses; only the convexity of $K$ is needed.
-- source:
--   Soyster, Convex Programming with Set-Inclusive Constraints and Applications to Inexact Linear Programming, Operations Research 21 (1973), p. 1155 (PDF p. 3), LEMMA

import Mathlib
import Definitions.Def_SoysterInexactLP_Auxiliary_Problems
open Pointwise Matrix

namespace SoysterInexactLP.Auxiliary

theorem lemma_X_convex {m n : ℕ} (K : Fin n → Set (Fin m → ℝ))
    (R : Set (Fin m → ℝ)) (hne : ∀ j, (K j).Nonempty) (hconv : ∀ j, Convex ℝ (K j))
    (hRne : R.Nonempty) (hRconv : Convex ℝ R) :
    Convex ℝ (X K R) := by sorry

end SoysterInexactLP.Auxiliary
