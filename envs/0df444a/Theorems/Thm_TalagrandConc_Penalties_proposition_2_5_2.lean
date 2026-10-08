-- Prove2me | Theorems.Thm_TalagrandConc_Penalties_proposition_2_5_2
-- name    : TalagrandConc.Penalties.proposition_2_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:40:58.91789+00:00
-- url     : https://prove2.me/theorems/87aa2098-fca8-4371-b745-6a83e2e131c5
-- title:
--   Proposition 2.5.2 — under (2.5.2), $\int e^{\hat g}\,d\mu \int e^{-g}\,d\mu \le e^{3t^2}$ for $\hat g = \inf_{s>0} s + t h(x,B_s)$
-- statement:
--   Let $(\Omega,\mu)$ be a probability space and $h : \Omega \times \Omega \to [0,\infty)$ measurable with $h(\omega,\omega) = 0$. For $B \subseteq \Omega$ let $h(\omega,B) = \inf\{h(\omega,\omega') ; \omega' \in B\}$ (with $h(\omega,\emptyset) = +\infty$). Assume that for each subset $B$ of $\Omega$,
--   $$\int_\Omega \exp 2h(x,B)\, d\mu(x) \;\le\; \frac{e}{\mu(B)}. \tag{2.5.2}$$
--   Consider $0 \le t \le 1$ and a measurable function $g \ge 0$ on $\Omega$. For $s \ge 0$ set $B_s = \{g \le s\}$ and
--   $$\hat g(x) = \inf_{s > 0}\ s + t\,h(x,B_s),$$
--   assumed measurable. Then
--   $$\int_\Omega e^{\hat g}\, d\mu \int_\Omega e^{-g}\, d\mu \;\le\; e^{3t^2}.$$
--
--   This is the one-coordinate step of the induction proving Theorem 2.5.1, the analogue of Proposition 2.4.2 when exponential integrability of $h$ is replaced by the weaker condition (2.5.2) on the set functional $h(x,B)$.
--
--   **Formalization Note** $h(x,B)$ and $\hat g$ take values in $[0,\infty]$ and $e^{+\infty} = +\infty$; $e/\mu(B) = +\infty$ when $\mu(B) = 0$. Because $x \mapsto h(x,B)$ need not be measurable, the integral in (2.5.2) is the upper integral $\int^*$, as the paper prescribes when measurability fails (pp. 81–82). Condition (2.5.2) covers every subset $B$, including nonmeasurable ones. The measurability of $\hat g$ is assumed, as in the proof of Proposition 2.4.2 which this proof follows.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 95, Proposition 2.5.2, Eq. (2.5.7)–(2.5.8); condition (2.5.2) on p. 94

import Mathlib
import Definitions.Def_TalagrandConc_Penalties_Basic

open MeasureTheory

namespace TalagrandConc.Penalties

theorem proposition_2_5_2
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ) (h_nonneg : ∀ x y, 0 ≤ h x y) (h_diag : ∀ x, h x x = 0)
    (h_meas : Measurable (Function.uncurry h))
    (h_cond : ∀ B : Set Ω,
      upperLIntegral μ (fun x => EReal.exp (2 * (hSet h x B : EReal)))
        ≤ ENNReal.ofReal (Real.exp 1) / μ B)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (g : Ω → ℝ) (g_nonneg : ∀ x, 0 ≤ g x) (g_meas : Measurable g)
    (ghat_meas : Measurable (ghatLevel t h g)) :
    (∫⁻ x, EReal.exp (ghatLevel t h g x : EReal) ∂μ) *
        (∫⁻ x, ENNReal.ofReal (Real.exp (-g x)) ∂μ)
      ≤ ENNReal.ofReal (Real.exp (3 * t ^ 2)) := by sorry

end TalagrandConc.Penalties
