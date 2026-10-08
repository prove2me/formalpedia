-- Prove2me | Theorems.Thm_TalagrandConc_ConvexHull_thm_4_3_1
-- name    : TalagrandConc.ConvexHull.thm_4_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:42:36.48909+00:00
-- url     : https://prove2.me/theorems/e2de1eb0-a0ec-4d5c-8597-cfc3390c0472
-- title:
--   Theorem 4.3.1 — two-point space: $\int\exp\big(\frac{\alpha}{\alpha+1}f_c^2(A,x)\big)dP(x)\le P(A)^{-\alpha}$
-- statement:
--   Let $\Omega=\{0,1\}$, let $\mu$ be the uniform probability on $\Omega$, and let $P=\mu^{\otimes N}$ be the uniform probability on $\{0,1\}^N$. For each $\alpha\ge1$ and each subset $A$ of $\Omega^N$,
--   $$\int\exp\Big(\frac{\alpha}{\alpha+1}f_c^2(A,x)\Big)\,dP(x)\le\frac{1}{P(A)^{\alpha}},$$
--   where $f_c(A,x)$ is the convex hull distance of Section 4.1.
--
--   Compared with (4.2.6), which yields the exponent $\frac{\alpha}{2(\alpha+1)}f_c^2$ on a general product space, the two-point space with the uniform measure gains a factor $2$ in the exponent.
--
--   **Formalization Note** $\{0,1\}$ is modelled by `Bool` and $\mu$ by `PMF.uniformOfFintype Bool`; every subset of the finite space $\{0,1\}^N$ is measurable, so no measurability hypothesis is needed. The integrand $\exp(\cdot)$ is computed in $[0,\infty]$ and is $+\infty$ when $A=\varnothing$; $P(A)^{-\alpha}=+\infty$ when $P(A)=0$.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 130, Theorem 4.3.1, Eq. (4.3.7)

import Mathlib
import Definitions.Def_TalagrandConc_ConvexHull_Basic

namespace TalagrandConc.ConvexHull

open MeasureTheory
open scoped ENNReal

/-- Talagrand (1995), p. 130, Theorem 4.3.1, Eq. (4.3.7): when `Ω = {0, 1}` (here `Bool`) and
`μ` is uniform, for each `α ≥ 1` and each `A ⊆ Ω^N`,
`∫ exp((α/(α + 1)) f_c²(A, x)) dP(x) ≤ P(A)^{−α}`, with `P = μ^{⊗N}`.
Every subset of the finite space `Bool^N` is measurable. -/
theorem thm_4_3_1 (N : ℕ) (α : ℝ) (hα : 1 ≤ α) (A : Set (Fin N → Bool)) :
    ∫⁻ x, EReal.exp (((ENNReal.ofReal (α / (α + 1)) * fc A x ^ 2 : ℝ≥0∞)) : EReal)
        ∂(Measure.pi fun _ : Fin N => (PMF.uniformOfFintype Bool).toMeasure)
      ≤ (Measure.pi (fun _ : Fin N => (PMF.uniformOfFintype Bool).toMeasure) A) ^ (-α) := by sorry

end TalagrandConc.ConvexHull
