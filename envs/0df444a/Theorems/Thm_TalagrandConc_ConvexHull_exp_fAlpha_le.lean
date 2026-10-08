-- Prove2me | Theorems.Thm_TalagrandConc_ConvexHull_exp_fAlpha_le
-- name    : TalagrandConc.ConvexHull.exp_fAlpha_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:42:13.25406+00:00
-- url     : https://prove2.me/theorems/541ec0cb-1981-4500-a27d-fde38d78b253
-- title:
--   Theorem 4.2.4 — $\int\exp f_\alpha(A,x)\,dP(x)\le P(A)^{-\alpha}$
-- statement:
--   Let $(\Omega,\mu)$ be a probability space, $N\ge0$, and $P=\mu^{\otimes N}$ the product probability on $\Omega^N$. Let $\alpha>0$ and let $f_\alpha(A,x)=\inf\{\sum_{i\le N}\xi(\alpha,s_i);\ s\in V_A(x)\}$, where $V_A(x)$ is the convex hull of $U_A(x)$ and $\xi$ is the function of Eq. (4.2.1). Then for every subset $A$ of $\Omega^N$,
--   $$\int\exp f_\alpha(A,x)\,dP(x)\le\frac{1}{P(A)^{\alpha}}.$$
--
--   For $\alpha=1$, Lemma 4.2.2 gives $\xi(1,u)\ge u^2/4$, so the theorem contains Theorem 4.1.1, $\int\exp\frac14f_c^2(A,x)\,dP(x)\le1/P(A)$. For large $\alpha$, $\xi(\alpha,1)=\log(1+\alpha)$ is large and the theorem also controls how many coordinates of $x$ must be changed to reach $A$, recovering features of the $q$-point inequalities of Section 3.
--
--   **Formalization Note** $\Omega^N$ is `Fin N → Ω` and $P$ is `Measure.pi`. The paper ignores measurability (pp. 81–82); here this convention is stated as explicit hypotheses: $A$ is measurable and so is $x\mapsto f_\alpha(A,x)$. The integral is the Lebesgue integral `∫⁻` of a $[0,\infty]$-valued function, $\exp(+\infty)=+\infty$, and $P(A)^{-\alpha}=+\infty$ when $P(A)=0$. The case $\alpha=0$ is excluded: the paper's §4.2 allows $\alpha\ge0$, but at $\alpha=0$ the inequality is trivial for nonempty $A$ and, with $f_0(\varnothing,x)=+\infty$, false for $A=\varnothing$.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 127, Theorem 4.2.4, Eq. (4.2.5)

import Mathlib
import Definitions.Def_TalagrandConc_ConvexHull_Basic

namespace TalagrandConc.ConvexHull

open MeasureTheory
open scoped ENNReal

/-- Talagrand (1995), p. 127, Theorem 4.2.4, Eq. (4.2.5): for a probability space `(Ω, μ)`,
`P = μ^{⊗N}` on `Ω^N`, `α > 0` and `A ⊆ Ω^N`,
`∫ exp f_α(A, x) dP(x) ≤ P(A)^{−α}`.
Measurability convention (p. 81–82): `A` and `x ↦ f_α(A, x)` are assumed measurable.
`exp` of `+∞` is `+∞` (`EReal.exp`), and `0^{−α} = +∞` in `ℝ≥0∞`. -/
theorem exp_fAlpha_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : ℕ) (α : ℝ) (hα : 0 < α) (A : Set (Fin N → Ω)) (hA : MeasurableSet A)
    (hmeas : Measurable fun x => fAlpha α A x) :
    ∫⁻ x, EReal.exp ((fAlpha α A x : ℝ≥0∞) : EReal) ∂(Measure.pi fun _ : Fin N => μ)
      ≤ (Measure.pi (fun _ : Fin N => μ) A) ^ (-α) := by sorry

end TalagrandConc.ConvexHull
