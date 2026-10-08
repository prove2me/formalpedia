-- Prove2me | Theorems.Thm_TalagrandConc_Penalties_theorem_2_4_1
-- name    : TalagrandConc.Penalties.theorem_2_4_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:40:38.460258+00:00
-- url     : https://prove2.me/theorems/0134a0c3-00e4-4ce1-aee7-8195cb6b75b0
-- title:
--   Theorem 2.4.1 — $\int e^{t f_h(A,x)}\,dP \le P(A)^{-1}\big(\frac12\iint (e^{tv}+e^{-tv})\,d\mu\,d\mu\big)^N$
-- statement:
--   Let $(\Omega,\mu)$ be a probability space, $N \ge 0$, and $P = \mu^{\otimes N}$ the product probability on $\Omega^N$. Let $h : \Omega \times \Omega \to [0,\infty)$ be measurable with $h(\omega,\omega) = 0$ for all $\omega$, and let
--   $$f_h(A,x) = \inf\Big\{\sum_{i \le N} h(x_i,y_i) \;;\; y \in A\Big\}$$
--   be the penalized distance from $x \in \Omega^N$ to $A \subseteq \Omega^N$. Set $v(\omega,\omega') = \max(h(\omega,\omega'), h(\omega',\omega))$.
--
--   For each measurable $A \subseteq \Omega^N$ and each $t > 0$ with $\iint \exp t h(x,y)\, d\mu(x)\, d\mu(y) < \infty$,
--   $$\int_{\Omega^N} e^{t f_h(A,x)}\, dP(x) \;\le\; \frac{1}{P(A)} \Big( \frac12 \int_{\Omega^2} \big(e^{t v(\omega,\omega')} + e^{-t v(\omega,\omega')}\big)\, d\mu(\omega)\, d\mu(\omega') \Big)^N.$$
--
--   The theorem says that the penalized distance to a set of non-negligible measure has a finite exponential moment, with an explicit bound that factorizes over the coordinates. It is the basic estimate behind the Bernstein-type tail bounds of Theorem 2.4.3 and Corollaries 2.4.4–2.4.5, and it is used again in Chapter 11 of the memoir.
--
--   **Formalization Note** $f_h$ is computed in $[0,\infty]$ with $f_h(\emptyset,x) = +\infty$, $e^{t\cdot(+\infty)} = +\infty$, and $1/P(A) = +\infty$ when $P(A) = 0$; integrals are lower Lebesgue integrals of $[0,\infty]$-valued functions. The paper ignores measurability questions (pp. 81–82); here this convention is the explicit hypothesis that $x \mapsto f_h(A,x)$ is measurable. The finiteness condition is on the integral over $\mu \otimes \mu$, which equals the iterated integral by Tonelli's theorem.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 92, Theorem 2.4.1, Eq. (2.4.4); standing assumptions p. 91, Eq. (2.4.2), and p. 92

import Mathlib
import Definitions.Def_TalagrandConc_Penalties_Basic

open MeasureTheory

namespace TalagrandConc.Penalties

theorem theorem_2_4_1
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ) (h_nonneg : ∀ x y, 0 ≤ h x y) (h_diag : ∀ x, h x x = 0)
    (h_meas : Measurable (Function.uncurry h))
    (N : ℕ) (A : Set (Fin N → Ω)) (hA : MeasurableSet A) (hfA : Measurable (fh h A))
    (t : ℝ) (ht : 0 < t)
    (h_int : ∫⁻ p : Ω × Ω, ENNReal.ofReal (Real.exp (t * h p.1 p.2)) ∂(μ.prod μ) ≠ ⊤) :
    ∫⁻ x, EReal.exp ((t : EReal) * (fh h A x : EReal)) ∂(Measure.pi fun _ : Fin N => μ)
      ≤ ((Measure.pi fun _ : Fin N => μ) A)⁻¹ *
        ((1 / 2 : ENNReal) * ∫⁻ p : Ω × Ω,
          ENNReal.ofReal (Real.exp (t * vmax h p.1 p.2) + Real.exp (-(t * vmax h p.1 p.2)))
            ∂(μ.prod μ)) ^ N := by sorry

end TalagrandConc.Penalties
