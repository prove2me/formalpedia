-- Prove2me | Theorems.Thm_WildeQIT_ZhangAudenaert_entropy_le_log_card
-- name    : WildeQIT.ZhangAudenaert.entropy_le_log_card
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:56:13.602978+00:00
-- url     : https://prove2.me/theorems/6569d96d-12f5-4f3f-88d3-f9ddf60c54d4
-- title:
--   Property 10.1.5 (Maximum Value): $H(X)\le\log|\mathcal X|$, with equality iff $X$ is uniform
-- statement:
--   Let $X$ be a random variable taking values in a finite alphabet $\mathcal X$, with distribution $p_X$, and let $H(X)=-\sum_x p_X(x)\log p_X(x)$ be its entropy in bits. Then
--
--   $$
--   H(X)\le\log|\mathcal X|,
--   $$
--
--   and equality holds if and only if $X$ is uniform on $\mathcal X$, that is, $p_X(x)=1/|\mathcal X|$ for every $x\in\mathcal X$.
--
--   This is the maximum-entropy principle for finite alphabets: no distribution is more uncertain than the uniform one. It bounds every entropy appearing in the chapter, including the conditional entropies in Fano's inequality.
--
--   **Formalization Note** The alphabet is a finite type and $X$ is represented by its distribution (`WildeQIT.FinDist`); logarithms are base $2$.
--
--   Differences from the source: none.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Property 10.1.5, eq. (10.8), p. 292

import Mathlib
import Definitions.Def_WildeQIT_entropy

namespace WildeQIT.ZhangAudenaert

/-- **Property 10.1.5 (Maximum Value).**
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Property 10.1.5, (10.8),
p. 292: "The maximum value of the entropy `H(X)` for a random variable `X` taking values in an
alphabet `𝒳` is `log |𝒳|`: `H(X) ≤ log |𝒳|`. The inequality is saturated if and only if `X` is a
uniform random variable on `𝒳`."

**Formalization Note.** The alphabet is a finite type `α` and `X` is represented by its
distribution `p`; entropy is in bits (`Real.logb 2`), as in the published `WildeQIT.entropy`.
"Uniform" means `p(x) = 1/|α|` for every `x`. -/
theorem entropy_le_log_card {α : Type} [Fintype α] (p : FinDist α) :
    entropy p ≤ Real.logb 2 (Fintype.card α) ∧
      (entropy p = Real.logb 2 (Fintype.card α) ↔
        ∀ x, p.prob x = 1 / (Fintype.card α : ℝ)) := by sorry

end WildeQIT.ZhangAudenaert
