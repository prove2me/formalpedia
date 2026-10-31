-- Prove2me | Theorems.Thm_ScarceIdeas_eq_24
-- name    : ScarceIdeas.eq_24
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:17:52.676+00:00
-- url     : https://prove2.me/theorems/2308ffd3-7bea-458d-b4b8-a9b09ec88dcc
-- title:
--   (24): the equation of motion $p'=\frac{1}{F(p)}\bigl(\frac{m_2}{m_1}\int F-r(\frac vr-p)\bigr)$ (corrected: welfare (16))
-- statement:
--   Throughout, $r>0$ is the discount rate, $v/r$ the social value of filling the niche, $f$ a continuous probability density with $f>0$ on its support $[\underline c,\overline c]\subset[0,\infty)$ and distribution function $F$, $\underline c<v/r<\overline c$, and the prior $h_0$ of the arrival rate satisfies Assumption 1. Let $p(\phi)\in[\underline c,\overline c]$ satisfy (22), $V(\phi)=\frac{m_1(\phi)}{r}\int_{\underline c}^{p(\phi)}F(c)\,dc$, for every $\phi\ge0$. Then $p(\phi)>\underline c$ (so $F(p(\phi))>0$), $p$ is continuously differentiable on $[0,\infty)$, and
--
--   $$\frac{dp(\phi)}{d\phi}=\frac{1}{F(p(\phi))}\Bigl(\frac{m_2(\phi)}{m_1(\phi)}\int_{\underline c}^{p(\phi)}F(c)\,dc-r\Bigl(\frac vr-p(\phi)\Bigr)\Bigr).$$
--
--   This is the central equation of motion of the optimal reward; Lemma 3, Lemma 4 and the asymptotics of Theorem 3 are derived from it.
--
--   Differences from the source:
--
--   - correction: welfare (16): the integrand multiplies e^{−λϕ(t)} by h_{ϕ(t)}(λ) → V is the supremum of the corrected functional ∫ e^{−rt} (∫ λ h0(λ) e^{−λΦ(t)} dλ / Z(ϕ)) ∫_{c̲}^{u(t)} (v/r − c) f(c) dc dt (definition welfare); reason: h_{ϕ(t)} already contains e^{−λϕ(t)}, so (16) counts survival twice: for h0(λ) = e^{−λ} and F(p) = 1/2 the printed λ-integrand at ϕ(t) = 1 integrates to (1/2)·2/9, the Bayesian claim density is (1/2)·1/4; the corrected form is the limit of the Bellman recursion (17) used by every later step
--   - reading: maximisation over reward paths p(·) with p(t) ∈ [c̲, c̄] → supremum over measurable (on (0, ∞)) policies with values in [cL, cH] for t ≥ 0; reason: the paper names no policy class; measurability makes every integral a genuine one
--   - encoding: all ϕ; dV/dϕ, dp/dϕ → ϕ ≥ 0, derivatives within [0, ∞); reason: the state ϕ = ∫F ≥ 0 lives in ℝ₊ (the space S, p.36); one-sided derivatives at the boundary state 0
--   - reading: the optimal policy p(ϕ) → any p with values in [cL, cH] satisfying (22) at every ϕ ≥ 0; reason: p.23 calls it "the dynamically optimal reward p(ϕ) defined by (22)"; (22) has a unique root at each state (Theorem 3)
--   - generalization: (24) → also p(ϕ) > c̲ and p' continuous on [0, ∞); reason: both are proved in Part 2 (p.38: "p(ϕ) is continuously differentiable"); extra conclusions specializing to (24)
-- source:
--   Basov, Erkal, Minehart, Scotchmer, Scarcity of Ideas and Optimal R&D Policy, SSRN 4628270, §4.2, (24), p.22; Appendix, proof of Theorem 3, Part 2, (46)–(48), p.38

import Mathlib
import Definitions.Def_ScarceIdeas_CostDensity
import Definitions.Def_ScarceIdeas_Assumption1
import Definitions.Def_ScarceIdeas_valueFn
import Definitions.Def_ScarceIdeas_moment

namespace ScarceIdeas

/-- **The equation of motion (24) of the optimal reward.**
Basov, Erkal, Minehart, Scotchmer, *Scarcity of Ideas and Optimal R&D Policy*, SSRN 4628270,
§4.2, (24), p.22; Appendix, proof of Theorem 3, Part 2, (46)–(48), p.38.

Under the standing assumptions, let `p(ϕ) ∈ [c̲, c̄]` be the reward defined by (22),
`V(ϕ) = (m₁(ϕ)/r) ∫_{c̲}^{p(ϕ)} F(c) dc` for every `ϕ ≥ 0`. Then `p(ϕ) > c̲` (so `F(p(ϕ)) > 0`),
`p` is continuously differentiable on `[0, ∞)`, and

$$\frac{dp(\phi)}{d\phi}=\frac{1}{F(p(\phi))}\Bigl(\frac{m_2(\phi)}{m_1(\phi)}
\int_{\underline c}^{p(\phi)}F(c)\,dc-r\Bigl(\frac vr-p(\phi)\Bigr)\Bigr).$$

**Formalization Note** The optimal reward is identified through (22), as the paper does on p.23
("the dynamically optimal reward p(ϕ) defined by (22)"). Derivatives are within `[0, ∞)`. -/
theorem eq_24 (r v cL cH : ℝ) (f h0 : ℝ → ℝ) (hr : 0 < r) (hf : CostDensity cL cH f)
    (hvL : cL < v / r) (hvH : v / r < cH) (h0A : Assumption1 h0) (p : ℝ → ℝ)
    (hp : ∀ ϕ : ℝ, 0 ≤ ϕ → p ϕ ∈ Set.Icc cL cH ∧
      valueFn r v cL cH f h0 ϕ = moment h0 1 ϕ / r * ∫ c in cL..p ϕ, costCDF cL f c) :
    (∀ ϕ : ℝ, 0 ≤ ϕ → cL < p ϕ) ∧
    ∃ p' : ℝ → ℝ, ContinuousOn p' (Set.Ici 0) ∧
      ∀ ϕ : ℝ, 0 ≤ ϕ → HasDerivWithinAt p (p' ϕ) (Set.Ici 0) ϕ ∧
        p' ϕ = 1 / costCDF cL f (p ϕ) *
          (moment h0 2 ϕ / moment h0 1 ϕ * (∫ c in cL..p ϕ, costCDF cL f c) -
            r * (v / r - p ϕ)) := by sorry

end ScarceIdeas
