-- Prove2me | Theorems.Thm_TaoBR_localSmoothingConjecture
-- name    : TaoBR.localSmoothingConjecture
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-29T17:10:44.104303+00:00
-- url     : https://prove2.me/theorems/6d7eee73-95e2-4129-8905-cf3d6aee348f
-- title:
--   Conjecture 4.1 — local smoothing for the wave equation at p = 2n/(n−1)
-- statement:
--   For $n \ge 2$ and $p = 2n/(n-1)$: for every $\varepsilon > 0$ there is $C$ such that every Schwartz $f$ satisfies
--   $$\|u\|_{L^p(\mathbf R^n \times [1, 2])} \le C\|(1 + \sqrt{-\Delta})^\varepsilon f\|_{L^p(\mathbf R^n)},$$
--   where $u(x, t)$ is the solution of $(-\partial_t^2 + \Delta)u = 0$ with $u(x, 0) = f(x)$, $u_t(x, 0) = 0$, given by $\hat u(\xi, t) = \cos(2\pi t|\xi|)\hat f(\xi)$, and $(1 + \sqrt{-\Delta})^\varepsilon$ is the multiplier $(1 + 2\pi|\xi|)^\varepsilon$.
--
--   This is open for $n \ge 3$. The case $n = 2$ is a theorem of Guth, Wang and Zhang ([A sharp square function estimate for the cone in $\mathbf R^3$, Ann. of Math. 192 (2020) 551–581](https://doi.org/10.4007/annals.2020.192.2.6)).
--
--   *Formalization note.* The paper's "a solution of the homogeneous Cauchy problem" is the solution given by the Fourier formula (`waveSolution`); for Schwartz data, solutions of the Cauchy problem are unique.
-- source:
--   Tao, T., The Bochner–Riesz conjecture implies the restriction conjecture, Duke Math. J. 96 (1999) 363–375, https://doi.org/10.1215/S0012-7094-99-09610-2 (the author's preprint, https://www.math.ucla.edu/~tao/preprints/restriction.dvi, whose page numbers are used), p. 8, Conjecture 4.1 (open)

import Mathlib
import Definitions.Def_TaoBR

namespace TaoBR

theorem localSmoothingConjecture (n : ℕ) (hn : 2 ≤ n) : LocalSmoothingConjecture n := by
  sorry

end TaoBR
