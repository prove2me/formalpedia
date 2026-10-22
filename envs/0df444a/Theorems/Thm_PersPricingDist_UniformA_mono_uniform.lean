-- Prove2me | Theorems.Thm_PersPricingDist_UniformA_mono_uniform
-- name    : PersPricingDist.UniformA.mono_uniform
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T02:45:05.533143+00:00
-- url     : https://prove2.me/theorems/0f2aa48a-7248-409e-8d6d-ab43144acdbd
-- title:
--   §5.1, p. 13 — A’s uniform monopoly profit is $1/4$
-- statement:
--   If only A is active and charges one price $p$, it sells to consumers whose value $u_A(x)$ covers that price. Under the standing market assumptions,
--
--   $$\sup_{p\in\mathbb R}\Pi_U^m(p)=\Pi_U^m(1/2)=\frac14.$$
--
--   This establishes the mono-distribution benchmark used in both retail pricing regimes. **Formalization Note** The supremum is expressed as an upper bound for every real price together with attainment at $p=1/2$.
-- source:
--   Jullien, Reisinger & Rey, Personalized Pricing and Distribution Strategies, authors' manuscript of March 2022 (Management Science, doi:10.1287/mnsc.2022.4437; PDF sha256 25a6c84ac0c48c6720f6a9e1f9b1f1ec516412c31dac044ac84c1d4c72dfc253), p. 13 (PDF 15)

import Mathlib
import Definitions.Def_PersPricingDist_UniformA_Setting

namespace PersPricingDist.UniformA

/-- The uniform-price monopoly benchmark on p. 13. -/
theorem mono_uniform (M : Model) (hM : M.Standing) :
    (∀ p : ℝ, M.monoProfitU p ≤ (1 : ℝ) / 4) ∧
    M.monoProfitU ((1 : ℝ) / 2) = (1 : ℝ) / 4 := by sorry
end PersPricingDist.UniformA
