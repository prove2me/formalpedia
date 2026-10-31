-- Prove2me | Theorems.Thm_ScarceIdeas_eq_21_22
-- name    : ScarceIdeas.eq_21_22
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:17:55.059867+00:00
-- url     : https://prove2.me/theorems/649192c1-0fb5-4583-93d6-3c4aa262cd07
-- title:
--   (20)–(22): the optimal reward is the unique HJB maximiser and $V=\frac{m_1}{r}\int_{\underline c}^{p}F$ (corrected: welfare (16))
-- statement:
--   Throughout, $r>0$ is the discount rate, $v/r$ the social value of filling the niche, $f$ a continuous probability density with $f>0$ on its support $[\underline c,\overline c]\subset[0,\infty)$ and distribution function $F$, $\underline c<v/r<\overline c$, and the prior $h_0$ of the arrival rate satisfies Assumption 1. The value function $V$ is differentiable on $[0,\infty)$ with derivative $V'$, and for every $\phi\ge0$:
--
--   1. the bracket of the HJB equation, $p\mapsto m_1(\phi)\int_{\underline c}^{p}(v/r-c)f(c)dc-(r+m_1(\phi)F(p))V(\phi)+V'(\phi)F(p)$, has exactly one maximiser on $[\underline c,\overline c]$;
--   2. every maximiser $q$ satisfies $q>\underline c$, the first-order condition
--   $$0=m_1(\phi)f(q)\Bigl(\frac vr-q-V(\phi)\Bigr)+f(q)\frac{dV(\phi)}{d\phi}\qquad(20)$$
--   in its simplified form
--   $$V(\phi)=\frac vr-q+\frac{1}{m_1(\phi)}\frac{dV(\phi)}{d\phi}\qquad(21)$$
--   and the value–policy relation
--   $$V(\phi)=\frac{m_1(\phi)}{r}\int_{\underline c}^{q}F(c)\,dc .\qquad(22)$$
--
--   Relation (22) is the dynamic analogue of the static condition (9), with the expected arrival rate $m_1(\phi)$ in place of $\lambda$.
--
--   Differences from the source:
--
--   - correction: welfare (16): the integrand multiplies e^{−λϕ(t)} by h_{ϕ(t)}(λ) → V is the supremum of the corrected functional ∫ e^{−rt} (∫ λ h0(λ) e^{−λΦ(t)} dλ / Z(ϕ)) ∫_{c̲}^{u(t)} (v/r − c) f(c) dc dt (definition welfare); reason: h_{ϕ(t)} already contains e^{−λϕ(t)}, so (16) counts survival twice: for h0(λ) = e^{−λ} and F(p) = 1/2 the printed λ-integrand at ϕ(t) = 1 integrates to (1/2)·2/9, the Bayesian claim density is (1/2)·1/4; the corrected form is the limit of the Bellman recursion (17) used by every later step
--   - reading: maximisation over reward paths p(·) with p(t) ∈ [c̲, c̄] → supremum over measurable (on (0, ∞)) policies with values in [cL, cH] for t ≥ 0; reason: the paper names no policy class; measurability makes every integral a genuine one
--   - encoding: all ϕ; dV/dϕ, dp/dϕ → ϕ ≥ 0, derivatives within [0, ∞); reason: the state ϕ = ∫F ≥ 0 lives in ℝ₊ (the space S, p.36); one-sided derivatives at the boundary state 0
--   - reading: p(ϕ), the optimal reward policy in (20)–(22) → every maximiser q ∈ [cL, cH] of the HJB bracket at ϕ, together with existence and uniqueness of the maximiser; reason: (20) is the first-order condition of the maximisation in (19); Part 2 (p.37) establishes that the optimal policy is unique
--   - generalization: (20), (21) and (22) for p(ϕ) → also q > c̲; reason: proved in Part 2 (p.38: F(p(ϕ)) = 0 contradicts optimality); it adds a conclusion and specializes to (20)–(22)
-- source:
--   Basov, Erkal, Minehart, Scotchmer, Scarcity of Ideas and Optimal R&D Policy, SSRN 4628270, §4.2, (20)–(22), p.22; Appendix, proof of Theorem 3, Part 2, (43)–(45), p.37

import Mathlib
import Definitions.Def_ScarceIdeas_CostDensity
import Definitions.Def_ScarceIdeas_Assumption1
import Definitions.Def_ScarceIdeas_valueFn
import Definitions.Def_ScarceIdeas_hjbBracket

namespace ScarceIdeas

/-- **First-order condition (20)–(21) and the value–policy relation (22).**
Basov, Erkal, Minehart, Scotchmer, *Scarcity of Ideas and Optimal R&D Policy*, SSRN 4628270,
§4.2, (20)–(22), p.22; Appendix, proof of Theorem 3, Part 2, (43)–(45), p.37.

Under the standing assumptions, the value function `V` is differentiable on `[0, ∞)` with some
derivative `V'`, and for every state `ϕ ≥ 0`:
1. the HJB bracket `p ↦ H(ϕ, V(ϕ), V'(ϕ), p)` has exactly one maximiser on `[c̲, c̄]`;
2. every maximiser `q` satisfies `q > c̲`,
   $$0=m_1(\phi)f(q)\Bigl(\frac vr-q-V(\phi)\Bigr)+f(q)\frac{dV(\phi)}{d\phi}\quad(20),$$
   $$V(\phi)=\frac vr-q+\frac{1}{m_1(\phi)}\frac{dV(\phi)}{d\phi}\quad(21),\qquad
   V(\phi)=\frac{m_1(\phi)}{r}\int_{\underline c}^{q}F(c)\,dc\quad(22).$$

**Formalization Note** The optimal reward `p(ϕ)` of (21)–(22) is the maximiser in the HJB
equation (19)/(41); derivatives are within `[0, ∞)`. -/
theorem eq_21_22 (r v cL cH : ℝ) (f h0 : ℝ → ℝ) (hr : 0 < r) (hf : CostDensity cL cH f)
    (hvL : cL < v / r) (hvH : v / r < cH) (h0A : Assumption1 h0) :
    ∃ V' : ℝ → ℝ,
      (∀ ϕ : ℝ, 0 ≤ ϕ → HasDerivWithinAt (valueFn r v cL cH f h0) (V' ϕ) (Set.Ici 0) ϕ) ∧
      ∀ ϕ : ℝ, 0 ≤ ϕ →
        (∃! q : ℝ, q ∈ Set.Icc cL cH ∧ ∀ p ∈ Set.Icc cL cH,
          hjbBracket r v cL f h0 ϕ (valueFn r v cL cH f h0 ϕ) (V' ϕ) p ≤
            hjbBracket r v cL f h0 ϕ (valueFn r v cL cH f h0 ϕ) (V' ϕ) q) ∧
        ∀ q ∈ Set.Icc cL cH, (∀ p ∈ Set.Icc cL cH,
          hjbBracket r v cL f h0 ϕ (valueFn r v cL cH f h0 ϕ) (V' ϕ) p ≤
            hjbBracket r v cL f h0 ϕ (valueFn r v cL cH f h0 ϕ) (V' ϕ) q) →
          cL < q ∧
          0 = moment h0 1 ϕ * f q * (v / r - q - valueFn r v cL cH f h0 ϕ) + f q * V' ϕ ∧
          valueFn r v cL cH f h0 ϕ = v / r - q + 1 / moment h0 1 ϕ * V' ϕ ∧
          valueFn r v cL cH f h0 ϕ = moment h0 1 ϕ / r * ∫ c in cL..q, costCDF cL f c := by sorry

end ScarceIdeas
