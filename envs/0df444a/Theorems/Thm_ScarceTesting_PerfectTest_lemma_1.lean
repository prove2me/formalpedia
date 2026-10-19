-- Prove2me | Theorems.Thm_ScarceTesting_PerfectTest_lemma_1
-- name    : ScarceTesting.PerfectTest.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:10:25.371985+00:00
-- url     : https://prove2.me/theorems/b1661354-861e-4621-8674-7dcbbcada901
-- title:
--   Lemma 1, p. 11 — agents with µ ∈ (t_L,t_H) value the test and follow its result; µ ≤ t_L never act; µ ≥ t_H always act
-- statement:
--   Throughout, $0<c<1$ is the cost-to-benefit ratio of acting (seeking treatment), and a $(\varphi,\sigma)$-test has false positive rate $\varphi$ and true positive rate $\sigma$ with $0\le\varphi\le\sigma\le1$, $\sigma>0$ and $\varphi<1$. Write $P(T=1)=\mu\sigma+(1-\mu)\varphi$ and $P(T=0)=\mu(1-\sigma)+(1-\mu)(1-\varphi)$ for an agent with prior $\mu\in[0,1]$, and let $V_{test}$ be the value of the test (displays (2)–(4)).
--
--   1. **Medium likelihood.** If $t_L<\mu<t_H$, then $V_{test}(\mu)>0$, and $P(I=1\mid T=1)>c$ while $P(I=1\mid T=0)<c$: the agent acts after a positive result and does not act after a negative one.
--   2. **Low likelihood.** If $\mu\le t_L$, then $V_{test}(\mu)=0$, $P(I=1\mid T=1)\le c$, $P(I=1\mid T=0)\le c$ and $\mu\le c$: the agent does not request the test and never acts.
--   3. **High likelihood.** If $\mu\ge t_H$, then $V_{test}(\mu)=0$, $P(I=1\mid T=1)\ge c$, $P(I=1\mid T=0)\ge c$ and $\mu\ge c$: the agent does not request the test and always acts.
--
--   Lemma 1 identifies the agents who request a test with the interval $(t_L,t_H)$, which turns the demand for a test into $F(t_H)-F(t_L)$.
--
--   **Formalization Note** Each comparison of a posterior with $c$ is stated cross-multiplied, $c\,P(T=t)$ versus $P(I=1,T=t)$, so it is meaningful even when $P(T=t)=0$. "Does not take the test" is $V_{test}(\mu)=0$: agents request a test iff its value is positive. The conditions $\sigma>0$ and $\varphi<1$ keep the denominators of $t_L,t_H$ positive.
-- source:
--   Drakopoulos & Randhawa, Why Perfect Tests May Not Be Worth Waiting For: Information as a Commodity, SSRN 3565245 (version of January 13, 2021), Lemma 1, p. 11 (proof pp. 20–22; characterization of the three groups, p. 10)

import Mathlib
import Definitions.Def_ScarceTesting_PerfectTest_Setting

namespace ScarceTesting.PerfectTest

/-- Lemma 1, p. 11: medium-likelihood agents (`μ ∈ (t_L, t_H)`) obtain positive value from the test
and act iff the result is positive; low-likelihood agents (`μ ≤ t_L`) obtain no value and never act;
high-likelihood agents (`μ ≥ t_H`) obtain no value and always act. "Acts after result `t`" is
`P(I = 1 | T = t) ≥ c`, written cross-multiplied as `c · P(T = t) ≤ P(I = 1, T = t)`. -/
theorem lemma_1 (c φ σ μ : ℝ)
    (hc0 : 0 < c) (hc1 : c < 1) (hφ0 : 0 ≤ φ) (hφσ : φ ≤ σ) (hσ1 : σ ≤ 1)
    (hσ0 : 0 < σ) (hφ1 : φ < 1)
    (hμ : μ ∈ Set.Icc (0:ℝ) 1) :
    (tL c φ σ < μ → μ < tH c φ σ →
      0 < Vtest c φ σ μ ∧
      c * (μ * σ + (1 - μ) * φ) < μ * σ ∧
      μ * (1 - σ) < c * (μ * (1 - σ) + (1 - μ) * (1 - φ))) ∧
    (μ ≤ tL c φ σ →
      Vtest c φ σ μ = 0 ∧
      μ * σ ≤ c * (μ * σ + (1 - μ) * φ) ∧
      μ * (1 - σ) ≤ c * (μ * (1 - σ) + (1 - μ) * (1 - φ)) ∧
      μ ≤ c) ∧
    (tH c φ σ ≤ μ →
      Vtest c φ σ μ = 0 ∧
      c * (μ * σ + (1 - μ) * φ) ≤ μ * σ ∧
      c * (μ * (1 - σ) + (1 - μ) * (1 - φ)) ≤ μ * (1 - σ) ∧
      c ≤ μ) := by sorry

end ScarceTesting.PerfectTest
