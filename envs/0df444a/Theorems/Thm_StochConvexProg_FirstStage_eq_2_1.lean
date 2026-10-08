-- Prove2me | Theorems.Thm_StochConvexProg_FirstStage_eq_2_1
-- name    : StochConvexProg.FirstStage.eq_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:41:11.454342+00:00
-- url     : https://prove2.me/theorems/0b9521c9-97e5-440e-994d-1401842fbcab
-- title:
--   (2.1) — F(x, u) = F₁(x₁, u₁) + ∫ F₂(s, x₁, x₂(s), u₂(s)) σ(ds)
-- statement:
--   For every $x=(x_1,x_2)\in X=\mathbb R^{n_1}\times\mathcal L^\infty_{n_2}$ and every $u=(u_1,u_2)\in U=\mathbb R^{m_1}\times\mathcal L^\infty_{m_2}$, the perturbation functional of the two-stage stochastic convex program splits into a first-stage term and an integral of the second-stage integrand:
--   $$F(x,u)=F_1(x_1,u_1)+\int_S F_2\big(s,x_1,x_2(s),u_2(s)\big)\,\sigma(ds),$$
--   where $F_1$ and $F_2$ are given by (2.2)–(2.3) and the integral of the extended-real function is taken under the convention (2.4) ($+\infty$ unless majorized by a summable function).
--
--   This representation of $F$ as an integral functional is what lets the paper apply the theory of convex integral functionals to $F_2$; in particular it turns the essential objective $f=F(\cdot,0)$ into (3.1).
--
--   **Formalization Note** The standing assumptions are those of `Problem`; $\sigma$ is a probability measure. The sum is in `EReal`. The integral under the convention (2.4) is the published definition `DupacovaWets.Consistency.expect`: $+\infty$ if $\int\theta^+\,d\sigma=\infty$, and $\int\theta^+\,d\sigma-\int\theta^-\,d\sigma$ (real or $-\infty$) otherwise, with lower Lebesgue integrals of the positive and negative parts; for a measurable $\theta$, $\int\theta^+<\infty$ holds exactly when $\theta$ is majorized almost everywhere by a summable function, so this is the paper's convention.
-- source:
--   Rockafellar and Wets, Stochastic convex programming: basic duality, Pacific J. Math. 62(1) (1976), p. 180, (2.1)–(2.3)

import Mathlib
import Definitions.Def_StochConvexProg_FirstStage_Problem
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_StochConvexProg_FirstStage_FirstStage

open MeasureTheory

namespace StochConvexProg.FirstStage

/-- (2.1), p. 180: `F(x, u) = F₁(x₁, u₁) + ∫_S F₂(s, x₁, x₂(s), u₂(s)) σ(ds)`, the integral taken
under the convention (2.4). -/
theorem eq_2_1 {S : Type*} [MeasurableSpace S] {σ : Measure S} [IsProbabilityMeasure σ]
    {n₁ n₂ m₁ m₂ : ℕ} (pr : Problem S σ n₁ n₂ m₁ m₂) :
    ∀ (x : StochConvexProg.Duality.XSpace σ n₁ n₂) (u : StochConvexProg.Duality.USpace σ m₁ m₂),
      pr.F x u = pr.F₁ x.1 u.1 + DupacovaWets.Consistency.expect σ (fun s => pr.F₂ s x.1 (x.2 s) (u.2 s)) := by sorry

end StochConvexProg.FirstStage
