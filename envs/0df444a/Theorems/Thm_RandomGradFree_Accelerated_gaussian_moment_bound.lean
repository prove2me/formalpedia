-- Prove2me | Theorems.Thm_RandomGradFree_Accelerated_gaussian_moment_bound
-- name    : RandomGradFree.Accelerated.gaussian_moment_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:06:51.812933+00:00
-- url     : https://prove2.me/theorems/31b1f0a9-c3c1-4bd7-9042-eb7f1cd3d454
-- title:
--   Lemma 1 — Gaussian moment bounds $M_p \le n^{p/2}$ ($p\in[0,2]$), $n^{p/2} \le M_p \le (p+n)^{p/2}$ ($p \ge 2$)
-- statement:
--   Let $E$ be a real inner product space of dimension $n$ and let $M_p = \mathbb E_u\|u\|^p$ be the $p$-th moment of the norm of a standard Gaussian vector $u$ in $E$. Then
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
--   These bounds are used to control the second moment of the random gradient-free oracle, in particular through $M_6 \le (n+6)^3$.
-- source:
--   Nesterov, Spokoiny, Random Gradient-Free Minimization of Convex Functions, Found. Comput. Math. 17 (2017), p. 534, Lemma 1, Eqs. (16)-(17)

import Mathlib
import Definitions.Def_RandomGradFree_Shared_moment

open MeasureTheory ProbabilityTheory

namespace RandomGradFree.Accelerated

theorem gaussian_moment_bound (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (p : ℝ) :
    (0 ≤ p → p ≤ 2 → RandomGradFree.Shared.moment E p ≤ (Module.finrank ℝ E : ℝ) ^ (p / 2)) ∧
    (2 ≤ p → (Module.finrank ℝ E : ℝ) ^ (p / 2) ≤ RandomGradFree.Shared.moment E p ∧
      RandomGradFree.Shared.moment E p ≤ (p + Module.finrank ℝ E) ^ (p / 2)) := by sorry

end RandomGradFree.Accelerated
