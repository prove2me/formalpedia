-- Prove2me | Theorems.Thm_SionMinimax_KKM_lemma_3_3
-- name    : SionMinimax.KKM.lemma_3_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:51:40.389982+00:00
-- url     : https://prove2.me/theorems/b371cb23-bf73-436b-a564-1f5135bebff5
-- title:
--   Lemma 3.3, p. 173 — for a minimal finite Y with each f(·, y) quasi-concave and u.s.c. on convex M, some μ₀ ∈ M has f(μ₀, y) < c for all y ∈ Y
-- statement:
--   Let $E$ be a real topological vector space, $M \subseteq E$ a nonempty convex set, $Y$ a finite set, $c$ a real number, and $f$ a real-valued function on $M \times Y$ such that, for each $y \in Y$,
--
--   1. $f(\cdot, y)$ is quasi-concave on $M$: every superlevel set $\{\mu \in M : f(\mu, y) \ge r\}$ is convex;
--   2. $f(\cdot, y)$ is upper semicontinuous on $M$, with respect to the topology $M$ inherits from $E$.
--
--   Suppose that $Y$ has the property *for each $\mu \in M$ there is a $y \in Y$ with $f(\mu, y) < c$*, and is minimal with this property: no proper subset of $Y$ has it. Then a single point of $M$ works for every $y$ at once: there is $\mu_0 \in M$ with
--
--   $$f(\mu_0, y) < c \quad \text{for all } y \in Y.$$
--
--   This lemma, together with its dual Lemma 3.3′, is the core of Sion's own proof of his minimax theorem (Theorem 3.4): after reducing to finite covers, a minimal finite set of strategies of one player can be beaten simultaneously by one strategy of the other.
--
--   **Formalization Note** $E$ carries the standard real topological vector space structure (topological additive group with continuous scalar multiplication), with no Hausdorff or finite-dimensionality assumption; "convex set" in the paper is read as a convex subset of such a space. The function is typed as $f : E \to \iota \to \mathbb R$ and $Y$ is a `Finset` of the index type $\iota$; every hypothesis refers only to points of $M$ and indices in $Y$, so the values of $f$ elsewhere are irrelevant. Minimality is encoded as: no strict sub-`Finset` $Y' \subset Y$ has the property. The hypothesis $M \neq \emptyset$ is added: for $M = Y = \emptyset$ the property and its minimality hold vacuously while no $\mu_0 \in M$ exists, so the printed statement fails in that corner. For nonempty $M$ the property already forces $Y \neq \emptyset$.
-- source:
--   Sion, On general minimax theorems, Pacific J. Math. 8(1) (1958) 171–176, p. 173 (PDF p. 4), Lemma 3.3

import Mathlib

namespace SionMinimax.KKM
theorem lemma_3_3 {E ι : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (M : Set E) (hM : Convex ℝ M) (hne : M.Nonempty)
    (Y : Finset ι) (f : E → ι → ℝ) (c : ℝ)
    (hq : ∀ y ∈ Y, QuasiconcaveOn ℝ M (fun μ => f μ y))
    (hu : ∀ y ∈ Y, UpperSemicontinuousOn (fun μ => f μ y) M)
    (hP : ∀ μ ∈ M, ∃ y ∈ Y, f μ y < c)
    (hmin : ∀ Y' : Finset ι, Y' ⊂ Y → ¬ ∀ μ ∈ M, ∃ y ∈ Y', f μ y < c) :
    ∃ μ₀ ∈ M, ∀ y ∈ Y, f μ₀ y < c := by sorry
end SionMinimax.KKM
