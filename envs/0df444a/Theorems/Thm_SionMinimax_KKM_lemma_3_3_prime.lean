-- Prove2me | Theorems.Thm_SionMinimax_KKM_lemma_3_3_prime
-- name    : SionMinimax.KKM.lemma_3_3_prime
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:51:40.161501+00:00
-- url     : https://prove2.me/theorems/ad28938a-57bf-4552-ac0c-058da43e41de
-- title:
--   Lemma 3.3′, p. 173 — dual: for a minimal finite X with each f(x, ·) quasi-convex and l.s.c. on convex N, some ν₀ ∈ N has f(x, ν₀) > c for all x ∈ X
-- statement:
--   Let $E$ be a real topological vector space, $N \subseteq E$ a nonempty convex set, $X$ a finite set, $c$ a real number, and $f$ a real-valued function on $X \times N$ such that, for each $x \in X$,
--
--   1. $f(x, \cdot)$ is quasi-convex on $N$: every sublevel set $\{\nu \in N : f(x, \nu) \le r\}$ is convex;
--   2. $f(x, \cdot)$ is lower semicontinuous on $N$, with respect to the topology $N$ inherits from $E$.
--
--   Suppose that $X$ has the property *for each $\nu \in N$ there is an $x \in X$ with $f(x, \nu) > c$*, and is minimal with this property: no proper subset of $X$ has it. Then there is $\nu_0 \in N$ with
--
--   $$f(x, \nu_0) > c \quad \text{for all } x \in X.$$
--
--   This is the dual of Lemma 3.3 (exchange the roles of the two variables and of $<$ and $>$); Sion's proof of Theorem 3.4 uses both lemmas, one for each player.
--
--   **Formalization Note** Same conventions as Lemma 3.3: $E$ is a real topological vector space without further assumptions, $f : \iota \to E \to \mathbb R$, $X$ is a `Finset` of $\iota$, minimality means no strict sub-`Finset` has the property. The hypothesis $N \neq \emptyset$ is added, since for $N = X = \emptyset$ the hypotheses hold vacuously and the conclusion fails.
-- source:
--   Sion, On general minimax theorems, Pacific J. Math. 8(1) (1958) 171–176, p. 173 (PDF p. 4), Lemma 3.3′

import Mathlib

namespace SionMinimax.KKM
theorem lemma_3_3_prime {E ι : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (N : Set E) (hN : Convex ℝ N) (hne : N.Nonempty)
    (X : Finset ι) (f : ι → E → ℝ) (c : ℝ)
    (hq : ∀ x ∈ X, QuasiconvexOn ℝ N (fun ν => f x ν))
    (hl : ∀ x ∈ X, LowerSemicontinuousOn (fun ν => f x ν) N)
    (hP : ∀ ν ∈ N, ∃ x ∈ X, c < f x ν)
    (hmin : ∀ X' : Finset ι, X' ⊂ X → ¬ ∀ ν ∈ N, ∃ x ∈ X', c < f x ν) :
    ∃ ν₀ ∈ N, ∀ x ∈ X, c < f x ν₀ := by sorry
end SionMinimax.KKM
