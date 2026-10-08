-- Prove2me | Theorems.Thm_TalagrandConc_Penalties_proposition_2_4_2
-- name    : TalagrandConc.Penalties.proposition_2_4_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:40:37.288381+00:00
-- url     : https://prove2.me/theorems/7f75357e-1b70-488c-a209-e641d3f04d93
-- title:
--   Proposition 2.4.2 — $\int e^{\hat g}\,d\mu \int e^{-g}\,d\mu \le \frac12\iint (e^{tv}+e^{-tv})\,d\mu\,d\mu$
-- statement:
--   Let $(\Omega,\mu)$ be a probability space and $h : \Omega \times \Omega \to [0,\infty)$ a measurable function with $h(\omega,\omega) = 0$ for every $\omega$. Set $v(\omega,\omega') = \max(h(\omega,\omega'), h(\omega',\omega))$ and fix $t > 0$. Let $g \ge 0$ be a measurable function on $\Omega$, and set
--   $$\hat g(x) = \inf_{y \in \Omega} \big(g(y) + t\,h(x,y)\big),$$
--   assumed measurable. Then
--   $$\int_\Omega e^{\hat g}\, d\mu \int_\Omega e^{-g}\, d\mu \;\le\; \frac12 \int_{\Omega^2} \big(e^{t v(\omega,\omega')} + e^{-t v(\omega,\omega')}\big)\, d\mu(\omega)\, d\mu(\omega').$$
--
--   This one-coordinate inequality is the step that drives the induction over $N$ in Theorem 2.4.1: applied to $g$ with $e^{-g(\omega)}$ the measure of a section of $A$, it bounds the exponential moment of $f_h$ in dimension $N+1$ by that in dimension $N$.
--
--   **Formalization Note** Integrals are lower Lebesgue integrals of $[0,\infty]$-valued functions; the right-hand side may be $+\infty$, in which case the inequality is trivial. The measurability of $\hat g$ is the paper's assumption at the start of the proof ("For simplicity we assume $\hat g$ measurable"). The parameter $t > 0$ is the $t$ of Theorem 2.4.1, in whose context the proposition is stated; the exponential integrability condition of that theorem is not assumed here.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 92, Proposition 2.4.2, Eq. (2.4.5)–(2.4.6)

import Mathlib
import Definitions.Def_TalagrandConc_Penalties_Basic

open MeasureTheory

namespace TalagrandConc.Penalties

theorem proposition_2_4_2
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ) (h_nonneg : ∀ x y, 0 ≤ h x y) (h_diag : ∀ x, h x x = 0)
    (h_meas : Measurable (Function.uncurry h))
    (t : ℝ) (ht : 0 < t)
    (g : Ω → ℝ) (g_nonneg : ∀ x, 0 ≤ g x) (g_meas : Measurable g)
    (ghat_meas : Measurable (ghat t h g)) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (ghat t h g x)) ∂μ) *
        (∫⁻ x, ENNReal.ofReal (Real.exp (-g x)) ∂μ)
      ≤ (1 / 2 : ENNReal) * ∫⁻ p : Ω × Ω,
          ENNReal.ofReal (Real.exp (t * vmax h p.1 p.2) + Real.exp (-(t * vmax h p.1 p.2)))
            ∂(μ.prod μ) := by sorry

end TalagrandConc.Penalties
