-- Prove2me | Theorems.Thm_TalagrandConc_ConvexHull_lemma_4_2_2
-- name    : TalagrandConc.ConvexHull.lemma_4_2_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:42:10.682989+00:00
-- url     : https://prove2.me/theorems/16aaa113-6169-48db-8dd3-ce6495ab85c6
-- title:
--   Lemma 4.2.2 — $\xi(\alpha,\cdot)$ is increasing and convex on $[0,1]$ and $\xi(\alpha,u)\ge\frac{\alpha}{2(\alpha+1)}u^2$
-- statement:
--   Let $\alpha>0$ and let $\xi(\alpha,\cdot)$ be the function of Eq. (4.2.1). Then:
--
--   1. $\xi(\alpha,\cdot)$ is strictly increasing on $[0,1]$;
--   2. $\xi(\alpha,\cdot)$ is convex on $[0,1]$;
--   3. for every $u\in[0,1]$,
--   $$\xi(\alpha,u)\ge\frac{\alpha}{2(\alpha+1)}u^2.$$
--
--   The quadratic lower bound compares $f_\alpha(A,x)$ with $\frac{\alpha}{2(\alpha+1)}f_c^2(A,x)$, which turns Theorem 4.2.4 into the tail bound (4.2.6) for the convex hull distance.
--
--   **Formalization Note** "Increasing" is read as strictly increasing (`StrictMonoOn`), which holds for $\alpha>0$. $\alpha>0$ is assumed: for $\alpha=0$, $\xi(0,\cdot)\equiv0$ is not increasing.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 127, Lemma 4.2.2

import Mathlib
import Definitions.Def_TalagrandConc_ConvexHull_Basic

namespace TalagrandConc.ConvexHull

/-- Talagrand (1995), p. 127, Lemma 4.2.2: for `α > 0`, the function `ξ(α, ·)` is
(strictly) increasing and convex on `[0, 1]`, and `ξ(α, u) ≥ α u² / (2(α + 1))` for
`u ∈ [0, 1]`. -/
theorem lemma_4_2_2 (α : ℝ) (hα : 0 < α) :
    StrictMonoOn (xi α) (Set.Icc 0 1) ∧ ConvexOn ℝ (Set.Icc 0 1) (xi α) ∧
      ∀ u ∈ Set.Icc (0 : ℝ) 1, α / (2 * (α + 1)) * u ^ 2 ≤ xi α u := by sorry

end TalagrandConc.ConvexHull
