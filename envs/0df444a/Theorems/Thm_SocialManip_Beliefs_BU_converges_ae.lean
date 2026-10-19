-- Prove2me | Theorems.Thm_SocialManip_Beliefs_BU_converges_ae
-- name    : SocialManip.Beliefs.BU_converges_ae
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:30:09.34999+00:00
-- url     : https://prove2.me/theorems/0dbb2785-8269-427d-b8d5-036ab7179a15
-- title:
--   §3.2, p. 11 — under Assumption 1(i), an agent's personal experience BU_i(h_{i,t}) converges almost surely to a constant
-- statement:
--   Fix one agent with signal quality $p\in[1/2,1)$, a prior $q\in(0,1)$, organic and principal intensities $\lambda,\lambda^*>0$, a realized state $y$, an influence state $\hat y$, a targeting decision $x_i\in\{0,1\}$ and a state $y'$. Let $s_1,s_2,\dots$ be the agent's signals: independent random variables in $\{S,R\}$ on a probability space, each equal to $S$ with probability
--   $$\frac{\lambda^*\,\mathbf 1[\hat y=S]+\lambda\,\mathbb P(s=S\mid y)}{\lambda+\lambda^*}\ \text{ if } x_i=1,\qquad \mathbb P(s=S\mid y)\ \text{ if } x_i=0,$$
--   where $\mathbb P(s=S\mid y)$ is $p$ for $y=S$ and $1-p$ for $y=R$ (display (1) and p. 5). Assume Assumption 1(i), amenability to mislearning:
--   $$p<\frac{\lambda^*+\lambda}{2\lambda}.$$
--   Then there is a constant $c$ such that, almost surely, the personal experience $\mathrm{BU}_i(y'\mid h_{i,t})$ computed from $s_1,\dots,s_t$ converges to $c$ as $t\to\infty$.
--
--   This is the first ingredient of Theorem 2: the page denotes the limit $\mathrm{BU}_i(h_{i,\infty}(\mathbf x^*))$ and the belief limit is expressed through it.
--
--   **Formalization Note** The signals are independent and have the same law at every time (on a two-point space this makes them identically distributed). The constant $c$ is deterministic, as on the page ("converges almost surely to some constant"). Assumption 1(i) is a standing assumption of §3.2, where the sentence appears; it rules out a targeted agent whose signal equals $S$ with probability exactly $1/2$, for which $\mathrm{BU}_i$ oscillates and has no limit.
-- source:
--   Mostagir, Ozdaglar & Siderius, When Is Society Susceptible to Manipulation?, SSRN preprint 3474643 (version of 2020-06-08; Manag. Sci. 2022, doi:10.1287/mnsc.2021.4265), §3.2, p. 11, "By the martingale convergence theorem, it is clear that BU_i(h_{i,t}) converges almost surely to some constant BU_i(h_{i,∞}(x*))"; signal law (1) and the principal, p. 5; BU_i, p. 6; Assumption 1(i), p. 10

import Mathlib
import Definitions.Def_SocialManip_Beliefs_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace SocialManip.Beliefs

theorem BU_converges_ae {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (p q lam lamStar : ℝ) (y yhat y' : State) (xi : Bool)
    (hq : 0 < q ∧ q < 1) (hp : 1 / 2 ≤ p ∧ p < 1) (hlam : 0 < lam) (hlamStar : 0 < lamStar)
    (hA1i : p < (lamStar + lam) / (2 * lam))
    (h : ℕ → Ω → State) (hm : ∀ τ, Measurable (h τ)) (hind : iIndepFun h P)
    (hlaw : ∀ τ, P {ω | h τ ω = State.S} =
      ENNReal.ofReal (signalProbS p lam lamStar y yhat xi)) :
    ∃ c : ℝ, ∀ᵐ ω ∂P, Tendsto (fun t => BU p q (fun τ => h τ ω) t y') atTop (𝓝 c) := by sorry

end SocialManip.Beliefs
