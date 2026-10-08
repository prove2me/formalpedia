-- Prove2me | Theorems.Thm_TalagrandConc_Penalties_corollary_2_4_5
-- name    : TalagrandConc.Penalties.corollary_2_4_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:40:45.371298+00:00
-- url     : https://prove2.me/theorems/fc002fd5-ecfc-4bdc-97d7-90bac7b3588c
-- title:
--   Corollary 2.4.5 — Bernstein-type bound $P(f_h(A,\cdot)\ge u) \le P(A)^{-1}\exp(-\min(u^2/8N\|h\|_2^2,\, u/2\|h\|_\infty))$
-- statement:
--   Let $(\Omega,\mu)$, $N$, $P = \mu^{\otimes N}$, the penalty $h \ge 0$ (measurable, $h(\omega,\omega) = 0$) and the penalized distance $f_h(A,x)$ be as in Theorem 2.4.1. Assume that
--   $$\|h\|_\infty = \sup_{x,y \in \Omega} h(x,y)$$
--   is finite, and set $\|h\|_2 = \big(\iint_{\Omega^2} h^2(\omega,\omega')\, d\mu(\omega)\, d\mu(\omega')\big)^{1/2}$. Then for every measurable $A \subseteq \Omega^N$ and every $u$,
--   $$P\big(\{ f_h(A,\cdot) \ge u \}\big) \;\le\; \frac{1}{P(A)} \exp\Big( - \min\Big( \frac{u^2}{8N\|h\|_2^2},\ \frac{u}{2\|h\|_\infty} \Big) \Big).$$
--
--   The bound has the shape of Bernstein's inequality: a Gaussian tail governed by the $L^2$ size of the penalty for moderate $u$, and an exponential tail governed by its sup norm for large $u$.
--
--   **Formalization Note** Conventions as in Theorem 2.4.1. The supremum is over all pairs (not an essential supremum). The two quotients are computed in $[0,\infty]$, so a quotient $a/0$ with $a > 0$ is $+\infty$ and $e^{-\infty} = 0$; this is the paper's reading when $\|h\|_2 = 0$, $\|h\|_\infty = 0$ or $N = 0$, and avoids the junk value $a/0 = 0$ of real division. If $P(A)=0$, the bound is $+\infty$, preserving the paper's $1/P(A)$ convention even when the exponential factor is $0$. For $u < 0$ the quantity $u$ is read as $0$ inside the quotients, which gives the bound $1/P(A)$ (the left side is $1$ there, so nothing is lost).
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 93, Corollary 2.4.5, Eq. (2.4.14)

import Mathlib
import Definitions.Def_TalagrandConc_Penalties_Basic

open MeasureTheory

namespace TalagrandConc.Penalties

theorem corollary_2_4_5
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ) (h_nonneg : ∀ x y, 0 ≤ h x y) (h_diag : ∀ x, h x x = 0)
    (h_meas : Measurable (Function.uncurry h))
    (h_sup_fin : (⨆ x, ⨆ y, ENNReal.ofReal (h x y)) ≠ ⊤)
    (N : ℕ) (A : Set (Fin N → Ω)) (hA : MeasurableSet A) (hfA : Measurable (fh h A))
    (u : ℝ) :
    (Measure.pi fun _ : Fin N => μ) {x | ENNReal.ofReal u ≤ fh h A x}
      ≤ if (Measure.pi fun _ : Fin N => μ) A = 0 then ⊤ else
        ((Measure.pi fun _ : Fin N => μ) A)⁻¹ *
        EReal.exp (-((min
          (ENNReal.ofReal (u ^ 2) /
            (8 * (N : ENNReal) * ∫⁻ p : Ω × Ω, ENNReal.ofReal (h p.1 p.2 ^ 2) ∂(μ.prod μ)))
          (ENNReal.ofReal u / (2 * ⨆ x, ⨆ y, ENNReal.ofReal (h x y))) : ENNReal) : EReal)) := by sorry

end TalagrandConc.Penalties
