-- Prove2me | Theorems.Thm_SmoothAmbEq_Gaussian_pi_star_condition_i
-- name    : SmoothAmbEq.Gaussian.pi_star_condition_i
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-24T20:38:16.226648+00:00
-- url     : https://prove2.me/theorems/008229d4-0043-45e9-8f29-fe0d558c75e6
-- title:
--   Appendix G, p. 39 — π* of (5.12) satisfies condition (i) of Definition 5.1 (well-posed wealth equation)
-- statement:
--   Consider the Gaussian-prior model of §5: wealth $X$ evolves under the inside system with hypothetical drift $z\in\mathbb R$,
--   $$dX_s=\big[rX_s+\pi(s,X_s,\beta^z_s)(z-r)\big]\,ds+\pi(s,X_s,\beta^z_s)\,\sigma\,dW_s,\qquad d\beta^z_s=\frac{\zeta(s)}{\sigma^2}(z-\beta^z_s)\,ds+\frac{\zeta(s)}{\sigma}\,dW_s ,$$
--   where $\zeta(s)=\sigma^2\sigma_0^2/(\sigma^2+s\sigma_0^2)$ is the posterior variance. Assume $\alpha>\max\{\alpha^*,1-0.5\sigma_0^{-2}\sigma^2T^{-1}\}$, and let $(m_1,\dots,m_6)$ solve (5.10) on $[0,T]$ with $\zeta(t)^{-1}-\alpha m_3(t)>0$. Let
--   $$\pi^*(t,x,\beta)=\frac{e^{-r(T-t)}}{k\sigma^2}\big\{a_1(t,m_2(t),m_3(t))+\zeta(t)m_1(t)\big\}(\beta-r)\qquad(5.12).$$
--
--   Then $\pi^*$ satisfies condition (i) of Definition 5.1. That is, for every $z\in\mathbb R$ and every starting point $(t,x,\beta)\in[0,T]\times\mathbb R^2$:
--
--   1. the wealth equation (5.2) driven by $\pi^*$, started at $X_t=x$, $\beta^z_t=\beta$, has a strong solution on $[t,T]$;
--   2. any two such strong solutions are indistinguishable on $[t,T]$.
--
--   The paper uses this when it says, at the start of Appendix G, "Obvious, $\pi^*$ is admissible, by Proposition 5.2": Proposition 5.2 needs condition (i) together with the growth bound (5.6), and $\pi^*$ has linear growth in $\beta$. The equation is linear, because $\pi^*$ does not depend on wealth and is affine in the Gaussian process $\beta^z$.
--
--   **Formalization Note** Condition (i) is the predicate `AdmissibleI` of the mission's InsideSystem definition. A strong solution is understood as in `IsInsideWealth`: it is adapted to the natural filtration of $W_{t+\cdot}-W_t$, has a.s. continuous paths, has a square-integrable integrand, and its stochastic integral is an Itô integral in the sense of `EthierKurtz.HasBrownianItoIntegral`. The hypotheses are those of Theorem 5.5, in whose proof the claim is made.
-- source:
--   Guan, Liang, Xia, Equilibrium Portfolio Selection for Smooth Ambiguity Preferences, arXiv:2302.08181v1, p. 39, Appendix G ("Obvious, π* is admissible, by Proposition 5.2"), together with p. 15, Definition 5.1 (i) and (5.2)

import Mathlib
import Definitions.Def_SmoothAmbEq_Gaussian_Model
import Definitions.Def_SmoothAmbEq_Gaussian_InsideSystem
import Definitions.Def_SmoothAmbEq_Gaussian_Candidate

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace SmoothAmbEq.Gaussian

/-- Appendix G, p. 39 (used in "Obvious, π* is admissible, by Proposition 5.2"): under the
hypotheses of Theorem 5.5, the feedback strategy `π*` of (5.12) satisfies condition (i) of
Definition 5.1: for every drift `z` and every start `(t, x, β) ∈ [0, T] × ℝ²` the wealth equation
(5.2) driven by `π*` has a strong solution on `[t, T]`, unique up to indistinguishability. -/
theorem pi_star_condition_i (M : Model) (a : ℝ) (ha : IsAlphaStar M a)
    (hα : max a (1 - 1 / 2 * (M.σ ^ 2 / (M.σ₀ ^ 2 * M.T))) < M.α) (c : Coeffs)
    (hc : SolvesODE510 M c) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ) (hW : IsBrownianReal W P) :
    AdmissibleI M P W (piStar M c) := by sorry

end SmoothAmbEq.Gaussian
