-- Prove2me | Theorems.Thm_RandomGradFree_Nonsmooth_gaussian_moment_bound
-- name    : RandomGradFree.Nonsmooth.gaussian_moment_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T07:23:14.828093+00:00
-- url     : https://prove2.me/theorems/62585028-fa1e-4978-8666-29f8559ecb9a
-- title:
--   Lemma 1 — Gaussian moment bounds $M_p \le n^{p/2}$ ($p\in[0,2]$), $n^{p/2}\le M_p\le (p+n)^{p/2}$ ($p\ge2$)
-- statement:
--   Let $E$ be a real inner product space of dimension $n$, $u$ a standard Gaussian vector in $E$, and $M_p = \mathbb E_u\|u\|^p$. Then:
--
--   1. for $p \in [0,2]$,
--   $$
--   M_p \le n^{p/2};
--   $$
--   2. for $p \ge 2$,
--   $$
--   n^{p/2} \le M_p \le (p+n)^{p/2}.
--   $$
--
--   These bounds turn every moment of the Gaussian direction that appears in the variance of the gradient-free oracles into an explicit function of the dimension; $p = 1$ gives the approximation error of Gaussian smoothing and $p = 4$ the second moment of the oracle.
--
--   **Formalization Note** Powers are real powers (`Real.rpow`) and $n$ is `Module.finrank ℝ E`; no lower bound on $n$ is assumed (at $n = 0$ all bounds hold).
-- source:
--   Nesterov, Spokoiny, Random Gradient-Free Minimization of Convex Functions, Found. Comput. Math. 17 (2017), p. 534, Lemma 1, Eqs. (16)-(17)

import Mathlib
import Definitions.Def_RandomGradFree_Shared_moment

namespace RandomGradFree.Nonsmooth

theorem gaussian_moment_bound (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (p : ℝ) :
    (0 ≤ p → p ≤ 2 → RandomGradFree.Shared.moment E p ≤ (Module.finrank ℝ E : ℝ) ^ (p / 2)) ∧
    (2 ≤ p → (Module.finrank ℝ E : ℝ) ^ (p / 2) ≤ RandomGradFree.Shared.moment E p ∧
      RandomGradFree.Shared.moment E p ≤ (p + Module.finrank ℝ E) ^ (p / 2)) := by sorry

end RandomGradFree.Nonsmooth
