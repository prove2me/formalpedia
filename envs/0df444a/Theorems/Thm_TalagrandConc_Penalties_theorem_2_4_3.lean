-- Prove2me | Theorems.Thm_TalagrandConc_Penalties_theorem_2_4_3
-- name    : TalagrandConc.Penalties.theorem_2_4_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:40:37.955373+00:00
-- url     : https://prove2.me/theorems/093fd63e-f451-46c1-8fd5-cdb617d7ace6
-- title:
--   Theorem 2.4.3 — $\int e^{t f_h(A,x)}\,dP \le P(A)^{-1}\exp\big(Nt^2\iint (e^{h}+e^{-h}-2)\big)$ for $t \le 1$
-- statement:
--   Let $(\Omega,\mu)$, $N$, $P = \mu^{\otimes N}$, the penalty $h \ge 0$ (measurable, $h(\omega,\omega) = 0$) and the penalized distance $f_h(A,x)$ be as in Theorem 2.4.1. Assume
--   $$\iint_{\Omega^2} \exp h(x,y)\, d\mu(x)\, d\mu(y) < \infty. \tag{2.4.10}$$
--   Then for every measurable $A \subseteq \Omega^N$ and every $0 \le t \le 1$,
--   $$\int_{\Omega^N} e^{t f_h(A,x)}\, dP(x) \;\le\; \frac{1}{P(A)} \exp\Big( N t^2 \iint_{\Omega^2} \big(e^{h(\omega,\omega')} + e^{-h(\omega,\omega')} - 2\big)\, d\mu(\omega)\, d\mu(\omega') \Big).$$
--
--   This is the simplified, Gaussian-in-$t$ form of Theorem 2.4.1, from which tail bounds for $f_h(A,\cdot)$ follow by Chebyshev's inequality.
--
--   **Formalization Note** Conventions as in Theorem 2.4.1 ($[0,\infty]$-valued $f_h$, $1/P(A) = +\infty$ when $P(A) = 0$, measurability of $f_h(A,\cdot)$ as a hypothesis). The paper writes "for $t \le 1$" with $t > 0$ understood from Theorem 2.4.1; the statement here takes $0 \le t \le 1$. The double integral of the non-negative function $e^{h}+e^{-h}-2$ is finite under (2.4.10) and is converted to a real number before exponentiation.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 93, Theorem 2.4.3, Eq. (2.4.10)–(2.4.11)

import Mathlib
import Definitions.Def_TalagrandConc_Penalties_Basic

open MeasureTheory

namespace TalagrandConc.Penalties

theorem theorem_2_4_3
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ) (h_nonneg : ∀ x y, 0 ≤ h x y) (h_diag : ∀ x, h x x = 0)
    (h_meas : Measurable (Function.uncurry h))
    (h_int : ∫⁻ p : Ω × Ω, ENNReal.ofReal (Real.exp (h p.1 p.2)) ∂(μ.prod μ) ≠ ⊤)
    (N : ℕ) (A : Set (Fin N → Ω)) (hA : MeasurableSet A) (hfA : Measurable (fh h A))
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∫⁻ x, EReal.exp ((t : EReal) * (fh h A x : EReal)) ∂(Measure.pi fun _ : Fin N => μ)
      ≤ ((Measure.pi fun _ : Fin N => μ) A)⁻¹ *
        ENNReal.ofReal (Real.exp ((N : ℝ) * t ^ 2 *
          (∫⁻ p : Ω × Ω, ENNReal.ofReal
              (Real.exp (h p.1 p.2) + Real.exp (-h p.1 p.2) - 2) ∂(μ.prod μ)).toReal)) := by sorry

end TalagrandConc.Penalties
