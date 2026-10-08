-- Prove2me | Theorems.Thm_SionMinimax_KKM_theorem_3_1
-- name    : SionMinimax.KKM.theorem_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:51:37.620064+00:00
-- url     : https://prove2.me/theorems/551e20b5-c8e4-4c79-8b3e-d74bf244cc0d
-- title:
--   Theorem 3.1, p. 173 — open-cover KKM theorem: open A_i covering a simplex, S − A_i convex, a_i ∉ A_j (i ≠ j) ⇒ ⋂ A_i ≠ ∅
-- statement:
--   Let $E$ be a real topological vector space and let $S \subseteq E$ be an $n$-dimensional simplex with vertices $a_0, \dots, a_n$, that is, $S$ is the convex hull of $n+1$ affinely independent points. Let $A_0, \dots, A_n \subseteq E$ be sets such that
--
--   1. each $A_i$ is open in $E$;
--   2. $S \subseteq \bigcup_{i=0}^n A_i$;
--   3. $S - A_i$ is convex for every $i$;
--   4. $a_i \notin A_j$ whenever $i \neq j$.
--
--   Then the sets have a common point:
--
--   $$\bigcap_{i=0}^{n} A_i \neq \emptyset.$$
--
--   This is an open-set version of the theorem of Knaster, Kuratowski and Mazurkiewicz. In the proof of Sion's Lemma 3.3 it is applied to the strict sublevel sets $A_i = \{\mu : f(\mu, y_i) < c\}$, which are open relative to the convex set $M$, on a simplex spanned inside $M$.
--
--   **Formalization Note** Openness is ambient openness in $E$, and the conclusion is the nonempty intersection printed on the page. The strict sublevel sets used in Lemma 3.3 are open relative to $M$; applying this theorem there requires an open ambient representative when restricting to the simplex. No Hausdorff or finite-dimensionality assumption is placed on $E$.
-- source:
--   Sion, On general minimax theorems, Pacific J. Math. 8(1) (1958) 171–176, p. 173 (PDF p. 4), Theorem 3.1

import Mathlib

namespace SionMinimax.KKM
theorem theorem_3_1 {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (n : ℕ) (a : Fin (n + 1) → E) (haff : AffineIndependent ℝ a)
    (A : Fin (n + 1) → Set E)
    (hA : ∀ i, IsOpen (A i))
    (hcov : convexHull ℝ (Set.range a) ⊆ ⋃ i, A i)
    (hconv : ∀ i, Convex ℝ (convexHull ℝ (Set.range a) \ A i))
    (hv : ∀ i j, i ≠ j → a i ∉ A j) :
    (⋂ i, A i).Nonempty := by sorry
end SionMinimax.KKM
