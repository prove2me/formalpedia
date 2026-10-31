-- Prove2me | Theorems.Thm_ScarceIdeas_lemma_3
-- name    : ScarceIdeas.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:16:18.181011+00:00
-- url     : https://prove2.me/theorems/c51fbe73-613c-4c49-9a0a-dd9791f71448
-- title:
--   Lemma 3: if $p'(\phi_1)=0$ then $p''(\phi_1)<0$
-- statement:
--   Throughout, $r>0$ is the discount rate, $v/r$ the social value of filling the niche, $f$ a continuous probability density with $f>0$ on its support $[\underline c,\overline c]\subset[0,\infty)$ and distribution function $F$, $\underline c<v/r<\overline c$, and the prior $h_0$ of the arrival rate satisfies Assumption 1. Let $p$ be twice differentiable on $[0,\infty)$, with first and second derivatives $p'$, $p''$ and values in $(\underline c,\overline c]$, and suppose it satisfies the equation of motion (24),
--
--   $$F(p(\phi))\,p'(\phi)=\frac{m_2(\phi)}{m_1(\phi)}\int_{\underline c}^{p(\phi)}F(c)\,dc-r\Bigl(\frac vr-p(\phi)\Bigr)\qquad(\phi\ge0).$$
--
--   Then for any $\phi_1\ge0$ with $p'(\phi_1)=0$, we have $p''(\phi_1)<0$.
--
--   Every critical point of the reward path is a strict local maximum; this rules out a reward that first falls and then rises, the step of the proof of Theorem 3 that makes the reward monotone.
--
--   Differences from the source:
--
--   - encoding: all ϕ; dV/dϕ, dp/dϕ → ϕ ≥ 0, derivatives within [0, ∞); reason: the state ϕ = ∫F ≥ 0 lives in ℝ₊ (the space S, p.36); one-sided derivatives at the boundary state 0
--   - generalization: the optimal reward policy p → every p twice differentiable on [0, ∞) with values in (c̲, c̄] satisfying (24); reason: the proof uses only (48) and Lemma 2; the optimal reward is such a p (eq_24, p > c̲, and p'' continuous by Part 2, p.38)
--   - encoding: (24) as a quotient by F(p(ϕ)) → (24) multiplied through by F(p(ϕ)); reason: F(p(ϕ)) > 0 for p(ϕ) > c̲, so the two forms are equivalent
-- source:
--   Basov, Erkal, Minehart, Scotchmer, Scarcity of Ideas and Optimal R&D Policy, SSRN 4628270, Lemma 3, Appendix p.39 (proof headed "Proof of Lemma 6", same page)

import Mathlib
import Definitions.Def_ScarceIdeas_CostDensity
import Definitions.Def_ScarceIdeas_Assumption1
import Definitions.Def_ScarceIdeas_moment
import Definitions.Def_ScarceIdeas_costCDF

namespace ScarceIdeas

/-- **Lemma 3: at a critical point of the reward path, its second derivative is negative.**
Basov, Erkal, Minehart, Scotchmer, *Scarcity of Ideas and Optimal R&D Policy*, SSRN 4628270,
Lemma 3, Appendix p.39 (its proof, headed "Proof of Lemma 6", is on the same page).

Under the standing assumptions, let `p` be twice differentiable on `[0, ∞)` (first and second
derivatives `p'`, `p''`), with values in `(c̲, c̄]`, satisfying the equation of motion (24) in the
form
$$F(p(\phi))\,p'(\phi)=\frac{m_2(\phi)}{m_1(\phi)}\int_{\underline c}^{p(\phi)}F(c)\,dc
-r\Bigl(\frac vr-p(\phi)\Bigr)\qquad(\phi\ge0).$$
Then for any `ϕ₁ ≥ 0` with `p'(ϕ₁) = 0` we have `p''(ϕ₁) < 0`.

**Formalization Note** Stated for every such `p`; by (24) (milestone `eq_24`) the optimal reward
is one. (24) is multiplied through by `F(p(ϕ))`, which is positive for `p(ϕ) > c̲`. Derivatives
are within `[0, ∞)`. -/
theorem lemma_3 (r v cL cH : ℝ) (f h0 : ℝ → ℝ) (hr : 0 < r) (hf : CostDensity cL cH f)
    (hvL : cL < v / r) (hvH : v / r < cH) (h0A : Assumption1 h0) (p p' p'' : ℝ → ℝ)
    (hrange : ∀ ϕ : ℝ, 0 ≤ ϕ → p ϕ ∈ Set.Ioc cL cH)
    (hp : ∀ ϕ : ℝ, 0 ≤ ϕ → HasDerivWithinAt p (p' ϕ) (Set.Ici 0) ϕ)
    (hp' : ∀ ϕ : ℝ, 0 ≤ ϕ → HasDerivWithinAt p' (p'' ϕ) (Set.Ici 0) ϕ)
    (hode : ∀ ϕ : ℝ, 0 ≤ ϕ → costCDF cL f (p ϕ) * p' ϕ =
      moment h0 2 ϕ / moment h0 1 ϕ * (∫ c in cL..p ϕ, costCDF cL f c) - r * (v / r - p ϕ))
    (ϕ₁ : ℝ) (hϕ₁ : 0 ≤ ϕ₁) (hcrit : p' ϕ₁ = 0) :
    p'' ϕ₁ < 0 := by sorry

end ScarceIdeas
