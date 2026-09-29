-- Prove2me | Theorems.Thm_RandomGradFree_Smooth_gaussian_moment_bound
-- name    : RandomGradFree.Smooth.gaussian_moment_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T08:48:31.826306+00:00
-- url     : https://prove2.me/theorems/b3bc93f1-5fdc-4332-80bd-9d50a2296bf6
-- title:
--   Lemma 1 — Gaussian moment bounds $M_p \le n^{p/2}$ ($p\le2$), $n^{p/2}\le M_p\le(p+n)^{p/2}$ ($p\ge2$)
-- statement:
--   Let $E$ be a real inner product space of finite dimension $n$, $u$ a standard Gaussian vector in $E$, and $M_p = \mathbb E_u\|u\|^p$. Then:
--
--   1. for $p \in [0,2]$,
--   $$ M_p \le n^{p/2}; $$
--   2. for $p \ge 2$,
--   $$ n^{p/2} \le M_p \le (p+n)^{p/2}. $$
--
--   These bounds turn the second moments of the random oracles into explicit dimension-dependent constants; the case $p = 6$ produces the factor $(n+6)^3$ in the variance bound (35).
-- source:
--   Nesterov, Spokoiny, Random Gradient-Free Minimization of Convex Functions, Found. Comput. Math. 17 (2017), p. 534, Lemma 1, Eqs. (16)-(17)

import Mathlib
import Definitions.Def_RandomGradFree_Shared_moment

open MeasureTheory ProbabilityTheory

namespace RandomGradFree.Smooth

theorem gaussian_moment_bound (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (p : ℝ) :
    (0 ≤ p → p ≤ 2 → RandomGradFree.Shared.moment E p ≤ (Module.finrank ℝ E : ℝ) ^ (p / 2)) ∧
    (2 ≤ p → (Module.finrank ℝ E : ℝ) ^ (p / 2) ≤ RandomGradFree.Shared.moment E p ∧
      RandomGradFree.Shared.moment E p ≤ (p + Module.finrank ℝ E) ^ (p / 2)) := by sorry

end RandomGradFree.Smooth
