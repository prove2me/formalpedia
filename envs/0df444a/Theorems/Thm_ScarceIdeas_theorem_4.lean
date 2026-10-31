-- Prove2me | Theorems.Thm_ScarceIdeas_theorem_4
-- name    : ScarceIdeas.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:18:21.549312+00:00
-- url     : https://prove2.me/theorems/abfcda58-62ec-4acf-be7f-a828149b387e
-- title:
--   Theorem 4: the optimal reward is below the naive reward at $\lambda=m_1(\phi)$ (corrected: welfare (16))
-- statement:
--   Throughout, $r>0$ is the discount rate, $v/r$ the social value of filling the niche, $f$ a continuous probability density with $f>0$ on its support $[\underline c,\overline c]\subset[0,\infty)$ and distribution function $F$, $\underline c<v/r<\overline c$, and the prior $h_0$ of the arrival rate satisfies Assumption 1. Let $p(\phi)\in[\underline c,\overline c]$ be the optimal reward, defined by (22): $V(\phi)=\frac{m_1(\phi)}{r}\int_{\underline c}^{p(\phi)}F(c)\,dc$ for every $\phi\ge0$. If $q$ is the reward a planner would choose if the arrival rate were fixed at $\lambda=m_1(\phi)$, that is, $q$ solves
--
--   $$\frac vr-q=\frac{m_1(\phi)}{r}\int_{\underline c}^{q}F(c)\,dc ,\qquad(56)$$
--
--   then $p(\phi)<q$.
--
--   Learning makes the planner more conservative than a planner who treats the current expected arrival rate as known; the gap is the option value of the information carried by an unclaimed reward.
--
--   Differences from the source:
--
--   - correction: welfare (16): the integrand multiplies e^{−λϕ(t)} by h_{ϕ(t)}(λ) → V is the supremum of the corrected functional ∫ e^{−rt} (∫ λ h0(λ) e^{−λΦ(t)} dλ / Z(ϕ)) ∫_{c̲}^{u(t)} (v/r − c) f(c) dc dt (definition welfare); reason: h_{ϕ(t)} already contains e^{−λϕ(t)}, so (16) counts survival twice: for h0(λ) = e^{−λ} and F(p) = 1/2 the printed λ-integrand at ϕ(t) = 1 integrates to (1/2)·2/9, the Bayesian claim density is (1/2)·1/4; the corrected form is the limit of the Bellman recursion (17) used by every later step
--   - reading: maximisation over reward paths p(·) with p(t) ∈ [c̲, c̄] → supremum over measurable (on (0, ∞)) policies with values in [cL, cH] for t ≥ 0; reason: the paper names no policy class; measurability makes every integral a genuine one
--   - encoding: all ϕ; dV/dϕ, dp/dϕ → ϕ ≥ 0, derivatives within [0, ∞); reason: the state ϕ = ∫F ≥ 0 lives in ℝ₊ (the space S, p.36); one-sided derivatives at the boundary state 0
--   - reading: the optimal reward policy p(ϕ) → any p with values in [cL, cH] satisfying (22) at every ϕ ≥ 0; reason: p.23: "the dynamically optimal reward p(ϕ) defined by (22)"; (22) has a unique root at each state
--   - reading: the reward if the arrival rate were fixed at λ = m_1(ϕ) → any root q of (56) at λ = m_1(ϕ); reason: the proof (p.41): "From equation (8), pna(ϕ) is the unique solution to (56)"
--   - reading: lower → strictly lower, p(ϕ) < q; reason: the proof's Part 2 shows p_na(ϕ) > p(ϕ) for all ϕ; the strict reading is the stronger one
-- source:
--   Basov, Erkal, Minehart, Scotchmer, Scarcity of Ideas and Optimal R&D Policy, SSRN 4628270, Theorem 4, p.23; proof pp.41–42

import Mathlib
import Definitions.Def_ScarceIdeas_CostDensity
import Definitions.Def_ScarceIdeas_Assumption1
import Definitions.Def_ScarceIdeas_valueFn
import Definitions.Def_ScarceIdeas_moment
import Definitions.Def_ScarceIdeas_IsStaticReward

namespace ScarceIdeas

/-- **Theorem 4: the optimal reward is lower than the naive reward at `λ = m₁(ϕ)`.**
Basov, Erkal, Minehart, Scotchmer, *Scarcity of Ideas and Optimal R&D Policy*, SSRN 4628270,
Theorem 4, p.23; proof pp.41–42.

Under the standing assumptions, let `p(ϕ) ∈ [c̲, c̄]` be the optimal reward, defined by (22):
`V(ϕ) = (m₁(ϕ)/r) ∫_{c̲}^{p(ϕ)} F(c) dc` for every `ϕ ≥ 0`. If `q` is the reward a planner would
choose if the arrival rate were fixed at `λ = m₁(ϕ)`, i.e. `q` solves (56),
`v/r − q = (m₁(ϕ)/r) ∫_{c̲}^{q} F(c) dc`, then

$$p(\phi)<q .$$

**Formalization Note** The optimal reward is identified through (22), as the paper does on p.23
("the dynamically optimal reward p(ϕ) defined by (22)"); the naive reward is the root of (56), as
in the paper's proof. The inequality is strict, as the proof (Part 2) shows. -/
theorem theorem_4 (r v cL cH : ℝ) (f h0 : ℝ → ℝ) (hr : 0 < r) (hf : CostDensity cL cH f)
    (hvL : cL < v / r) (hvH : v / r < cH) (h0A : Assumption1 h0) (p : ℝ → ℝ)
    (hp : ∀ ϕ : ℝ, 0 ≤ ϕ → p ϕ ∈ Set.Icc cL cH ∧
      valueFn r v cL cH f h0 ϕ = moment h0 1 ϕ / r * ∫ c in cL..p ϕ, costCDF cL f c) :
    ∀ ϕ : ℝ, 0 ≤ ϕ → ∀ q : ℝ, IsStaticReward r v cL f (moment h0 1 ϕ) q → p ϕ < q := by sorry

end ScarceIdeas
