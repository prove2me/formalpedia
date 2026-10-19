-- Prove2me | Theorems.Thm_ScarceTesting_PerfectTest_simplified_objective
-- name    : ScarceTesting.PerfectTest.simplified_objective
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:10:31.638912+00:00
-- url     : https://prove2.me/theorems/1baf88db-72b1-4fe3-ace5-f2f143e5223b
-- title:
--   Proof of Proposition 2, p. 22 — the planner's objective S(φ,σ) as integrals over [c,1], [c,t_H] and [t_L,c]
-- statement:
--   Throughout, $0<c<1$ is the cost-to-benefit ratio of acting (seeking treatment), and a $(\varphi,\sigma)$-test has false positive rate $\varphi$ and true positive rate $\sigma$ with $0\le\varphi\le\sigma\le1$, $\sigma>0$ and $\varphi<1$. The prior density $f$ is a nonnegative integrable function on $[0,1]$ with total mass $1$, and $F(x)=\int_0^x f$. Let $0<\kappa<1$, $0\le\beta<1$, and let $A=A(t_L,t_H)=\min\{1,\kappa/(F(t_H)-F(t_L))\}$. The planner's objective $S(\varphi,\sigma)$ (display (9) with $\alpha=1$, defined from agents' behaviour) equals
--   $$S(\varphi,\sigma)=\int_c^1(\mu-\beta(1-\mu))\,dF(\mu)+\int_c^{t_H}A\big((1-\mu)\beta(1-\varphi)-\mu(1-\sigma)\big)\,dF(\mu)+\int_{t_L}^{c}A\big(\mu\sigma-(1-\mu)\beta\varphi\big)\,dF(\mu).$$
--
--   The first integral is the planner's payoff when nobody is tested; the other two are the changes caused by testing medium-likelihood agents above and below $c$. This closed form is the starting point of both parts of the proof of Proposition 2.
--
--   **Formalization Note** $dF(\mu)$ is $f(\mu)\,d\mu$. $S$ is defined by integrating each agent's expected contribution, not by this formula; the identity is the content of the step. The conditions $\sigma>0$, $\varphi<1$ keep $t_L,t_H$ well defined.
-- source:
--   Drakopoulos & Randhawa, Why Perfect Tests May Not Be Worth Waiting For: Information as a Commodity, SSRN 3565245 (version of January 13, 2021), proof of Proposition 2 (Appendix A.1.2), p. 22, "We first note that the planner's objective can be simplified to"

import Mathlib
import Definitions.Def_ScarceTesting_PerfectTest_Setting

namespace ScarceTesting.PerfectTest

/-- Proof of Proposition 2, p. 22: the planner's objective simplifies to
`S(φ,σ) = ∫_c^1 (μ − β(1−μ)) dF + ∫_c^{t_H} A((1−μ)β(1−φ) − μ(1−σ)) dF + ∫_{t_L}^c A(μσ − (1−μ)βφ) dF`
with `A = A(t_L, t_H)`. -/
theorem simplified_objective (f : ℝ → ℝ) (c β κ φ σ : ℝ)
    (hc0 : 0 < c) (hc1 : c < 1) (hφ0 : 0 ≤ φ) (hφσ : φ ≤ σ) (hσ1 : σ ≤ 1)
    (hσ0 : 0 < σ) (hφ1 : φ < 1)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hf : IsPriorDensity f) :
    S f c β κ φ σ =
      (∫ μ in c..1, (μ - β * (1 - μ)) * f μ) +
      (∫ μ in c..tH c φ σ, availThr f κ (tL c φ σ) (tH c φ σ) *
          ((1 - μ) * β * (1 - φ) - μ * (1 - σ)) * f μ) +
      (∫ μ in tL c φ σ..c, availThr f κ (tL c φ σ) (tH c φ σ) *
          (μ * σ - (1 - μ) * β * φ) * f μ) := by sorry

end ScarceTesting.PerfectTest
