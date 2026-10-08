-- Prove2me | Theorems.Thm_TalagrandConc_Penalties_corollary_2_4_4
-- name    : TalagrandConc.Penalties.corollary_2_4_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:40:51.816734+00:00
-- url     : https://prove2.me/theorems/69204a8b-0e55-4ae0-8ed1-9a273fef2332
-- title:
--   Corollary 2.4.4 — $P(f_h(A,\cdot) \ge u) \le P(A)^{-1} e^{-u^2/4N}$ for $u \le 2N$ when $\iint e^h \le 2$
-- statement:
--   Let $(\Omega,\mu)$, $N$, $P = \mu^{\otimes N}$, the penalty $h \ge 0$ (measurable, $h(\omega,\omega) = 0$) and the penalized distance $f_h(A,x)$ be as in Theorem 2.4.1. Assume
--   $$\iint_{\Omega^2} \exp h(x,y)\, d\mu(x)\, d\mu(y) \le 2. \tag{2.4.12}$$
--   Then for every measurable $A \subseteq \Omega^N$ and all $0 \le u \le 2N$,
--   $$P\big(\{ f_h(A,\cdot) \ge u \}\big) \;\le\; \frac{1}{P(A)}\, e^{-u^2/4N}.$$
--
--   This is a sub-Gaussian tail bound for the penalized distance in the range $u \le 2N$; it is used again in the study of the Sherrington–Kirkpatrick model in Chapter 12 of the memoir.
--
--   **Formalization Note** Conventions as in Theorem 2.4.1. The paper says "for all $u \le 2N$"; the restriction $u \ge 0$ is understood (for $u < 0$ the left side is $1$ and the bound can fail), and it is stated explicitly. At $N = 0$ the only admissible value is $u = 0$, where both sides are read with $0/0 = 0$, i.e. $e^{0} = 1$.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 93, Corollary 2.4.4, Eq. (2.4.12)–(2.4.13)

import Mathlib
import Definitions.Def_TalagrandConc_Penalties_Basic

open MeasureTheory

namespace TalagrandConc.Penalties

theorem corollary_2_4_4
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ) (h_nonneg : ∀ x y, 0 ≤ h x y) (h_diag : ∀ x, h x x = 0)
    (h_meas : Measurable (Function.uncurry h))
    (h_int : ∫⁻ p : Ω × Ω, ENNReal.ofReal (Real.exp (h p.1 p.2)) ∂(μ.prod μ) ≤ 2)
    (N : ℕ) (A : Set (Fin N → Ω)) (hA : MeasurableSet A) (hfA : Measurable (fh h A))
    (u : ℝ) (hu0 : 0 ≤ u) (hu : u ≤ 2 * N) :
    (Measure.pi fun _ : Fin N => μ) {x | ENNReal.ofReal u ≤ fh h A x}
      ≤ ((Measure.pi fun _ : Fin N => μ) A)⁻¹ *
        ENNReal.ofReal (Real.exp (-(u ^ 2) / (4 * N))) := by sorry

end TalagrandConc.Penalties
