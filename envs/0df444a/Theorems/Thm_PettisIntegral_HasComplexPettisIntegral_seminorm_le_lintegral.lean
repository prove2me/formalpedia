-- Prove2me | Theorems.Thm_PettisIntegral_HasComplexPettisIntegral_seminorm_le_lintegral
-- name    : PettisIntegral.HasComplexPettisIntegral.seminorm_le_lintegral
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:25:09.589579+00:00
-- url     : https://prove2.me/theorems/3f61fb0f-150c-4481-8a25-379789f6c633
-- title:
--   Lemma C.4.3.9 for complex measures — $\nu\bigl(\int_X f\,d\mu\bigr)\le\int_X\nu(f(x))\,d|\mu|(x)$
-- statement:
--   **Seminorm estimate for Pettis integrals against a complex measure (Lemma C.4.3.9, corrected).** Let $E$ be a Hausdorff locally convex space over $\mathbb C$, let $\mu$ be a complex measure on a measurable space $X$ with total variation $|\mu|$, and let $f\colon X\to E$ be $\mu$-integrable in the sense of Pettis, with integral $\int_X f\,d\mu\in E$. Then for every continuous seminorm $\nu$ on $E$ such that $x\mapsto\nu(f(x))$ is $|\mu|$-measurable,
--   $$\nu\Bigl(\int_X f\,d\mu\Bigr)\ \le\ \int_X\nu(f(x))\,d|\mu|(x).$$
--   The right-hand side is the integral of a non-negative measurable function against the positive measure $|\mu|$ and may be $+\infty$.
--
--   This is the triangle inequality for vector-valued integrals against complex measures, the tool for continuity statements about such integrals (for instance for contour integrals $\int_\Gamma f(\xi)\,d\xi$, where it bounds a seminorm of the integral by the length of $\Gamma$ times the supremum of the seminorm of $f$ on $\Gamma$).
--
--   **Deviation from the source.** The source prints the inequality with $d\mu$ on the right-hand side for a finite complex Radon measure $\mu$; then the right-hand side is a complex number and the inequality has no meaning (for $\mu=-\delta_x$ and $f=1$ it would read $1\le -1$). The total variation $|\mu|$ is what the proof gives and what is stated here.
--
--   **Formalization Note.** `HasComplexPettisIntegral μ f a` (from `Def_PettisIntegral_ComplexMeasure`) says that $a$ is the Pettis integral of $f$ against the complex measure `μ : ComplexMeasure X`, and `μ.variation` is $|\mu|$. The inequality is stated in $[0,\infty]$ with the lower Lebesgue integral: `ENNReal.ofReal (p a) ≤ ∫⁻ x, ENNReal.ofReal (p (f x)) ∂μ.variation`. "$|\mu|$-measurable" is `AEMeasurable`. "Hausdorff locally convex space" is `[IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E] [T2Space E]`. No topology on $X$ is involved (the source: $X$ locally compact Hausdorff, $\mu$ finite Radon).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 715, Lemma C.4.3.9 and Remark C.4.3.10; classical reference: a variant is given in N. Bourbaki, Elements of Mathematics, Integration I, Springer, Ch. VI, §1, no. 2, Prop. 6 (as cited by the paper)

import Mathlib
import Definitions.Def_PettisIntegral_Basic
import Definitions.Def_PettisIntegral_ComplexMeasure

open MeasureTheory

set_option autoImplicit false

namespace PettisIntegral

/-- A continuous seminorm of a Pettis integral against a complex measure is at most the integral
of the seminorm against the total variation of the measure. -/
theorem HasComplexPettisIntegral.seminorm_le_lintegral {E X : Type*} [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    [PolynormableSpace ℂ E] [T2Space E] [MeasurableSpace X] {μ : ComplexMeasure X}
    {f : X → E} {a : E}
    (ha : HasComplexPettisIntegral μ f a) (p : Seminorm ℂ E) (hp : Continuous p)
    (hpf : AEMeasurable (fun x => p (f x)) μ.variation) :
    ENNReal.ofReal (p a) ≤ ∫⁻ x, ENNReal.ofReal (p (f x)) ∂μ.variation := by sorry

end PettisIntegral
