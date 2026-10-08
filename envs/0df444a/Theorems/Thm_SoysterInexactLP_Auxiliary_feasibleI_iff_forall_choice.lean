-- Prove2me | Theorems.Thm_SoysterInexactLP_Auxiliary_feasibleI_iff_forall_choice
-- name    : SoysterInexactLP.Auxiliary.feasibleI_iff_forall_choice
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:37:07.628585+00:00
-- url     : https://prove2.me/theorems/af88a43c-e34c-41cc-8ec7-d6ada8bd9490
-- title:
--   Feasibility for (I) means x₁a₁+⋯+xₙaₙ ∈ K for every choice aⱼ ∈ Kⱼ
-- statement:
--   Let $K_1,\dots,K_n\subseteq\mathbb R^m$ be nonempty convex activity sets and $K\subseteq\mathbb R^m$ a nonempty convex resource set. A vector $x\in\mathbb R^n$ is feasible for problem (I), i.e. $x\ge0$ and $x_1K_1+\cdots+x_nK_n\subseteq K$, if and only if $x\ge 0$ and
--   $$x_1a_1+x_2a_2+\cdots+x_na_n\in K\qquad\text{for every choice of } a_1\in K_1,\dots,a_n\in K_n.$$
--
--   This unpacks the Minkowski-sum constraint into the "for every realisation of the activity vectors" form used in the rest of the paper.
--
--   **Formalization Note** Nonemptiness and convexity of the sets are the paper's standing assumptions (p. 1154) and are kept as hypotheses, although the equivalence holds for arbitrary sets.
-- source:
--   Soyster, Convex Programming with Set-Inclusive Constraints and Applications to Inexact Linear Programming, Operations Research 21 (1973), p. 1154 (PDF p. 2), sentence after (I)

import Mathlib
import Definitions.Def_SoysterInexactLP_Auxiliary_Problems
open Pointwise Matrix

namespace SoysterInexactLP.Auxiliary

theorem feasibleI_iff_forall_choice {m n : ℕ} (K : Fin n → Set (Fin m → ℝ))
    (R : Set (Fin m → ℝ)) (hne : ∀ j, (K j).Nonempty) (hconv : ∀ j, Convex ℝ (K j))
    (hRne : R.Nonempty) (hRconv : Convex ℝ R) (x : Fin n → ℝ) :
    FeasibleI K R x ↔
      (∀ j, 0 ≤ x j) ∧ ∀ a : Fin n → Fin m → ℝ, (∀ j, a j ∈ K j) → ∑ j, x j • a j ∈ R := by sorry

end SoysterInexactLP.Auxiliary
