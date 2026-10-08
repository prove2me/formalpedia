-- Prove2me | Theorems.Thm_TalagrandConc_Penalties_theorem_2_5_1
-- name    : TalagrandConc.Penalties.theorem_2_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:40:57.11301+00:00
-- url     : https://prove2.me/theorems/18e9515a-b735-4417-9cd7-8326dd82e2ca
-- title:
--   Theorem 2.5.1 — under (2.5.2), $\int e^{t f_h(A,x)}\,dP \le e^{3t^2N}/P(A)$ for $0 \le t \le 1$
-- statement:
--   Let $(\Omega,\mu)$ be a probability space, $N \ge 0$, $P = \mu^{\otimes N}$, and $h : \Omega \times \Omega \to [0,\infty)$ measurable with $h(\omega,\omega) = 0$; let $f_h(A,x)$ be the penalized distance of Theorem 2.4.1 and $h(\omega,B) = \inf\{h(\omega,\omega') ; \omega' \in B\}$. Assume that for each subset $B$ of $\Omega$,
--   $$\int_\Omega \exp 2h(x,B)\, d\mu(x) \;\le\; \frac{e}{\mu(B)}. \tag{2.5.2}$$
--   Then for each measurable $A \subseteq \Omega^N$ and each $0 \le t \le 1$,
--   $$\int_{\Omega^N} e^{t f_h(A,x)}\, dP(x) \;\le\; \frac{e^{3t^2 N}}{P(A)}.$$
--
--   Condition (2.5.2) is much weaker than the exponential integrability (2.4.10) of Theorem 2.4.3; for instance, when $\Omega$ is itself a product of $m$ spaces, $m^{-1/2}$ times the Hamming distance on $\Omega$ satisfies it. The theorem then shows that the coordinates a point misses in a set are concentrated in few blocks.
--
--   **Formalization Note** Conventions as in Theorem 2.4.1 and Proposition 2.5.2: $[0,\infty]$-valued $f_h$ and $h(x,B)$, $1/P(A) = +\infty$ when $P(A) = 0$, measurability of $f_h(A,\cdot)$ as a hypothesis, and the upper integral in (2.5.2), required for every subset $B$. The paper says "each subset $A$"; $A$ is taken measurable here.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 94, Theorem 2.5.1, Eq. (2.5.1)–(2.5.3)

import Mathlib
import Definitions.Def_TalagrandConc_Penalties_Basic

open MeasureTheory

namespace TalagrandConc.Penalties

theorem theorem_2_5_1
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ) (h_nonneg : ∀ x y, 0 ≤ h x y) (h_diag : ∀ x, h x x = 0)
    (h_meas : Measurable (Function.uncurry h))
    (h_cond : ∀ B : Set Ω,
      upperLIntegral μ (fun x => EReal.exp (2 * (hSet h x B : EReal)))
        ≤ ENNReal.ofReal (Real.exp 1) / μ B)
    (N : ℕ) (A : Set (Fin N → Ω)) (hA : MeasurableSet A) (hfA : Measurable (fh h A))
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∫⁻ x, EReal.exp ((t : EReal) * (fh h A x : EReal)) ∂(Measure.pi fun _ : Fin N => μ)
      ≤ ((Measure.pi fun _ : Fin N => μ) A)⁻¹ *
        ENNReal.ofReal (Real.exp (3 * t ^ 2 * N)) := by sorry

end TalagrandConc.Penalties
